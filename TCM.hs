{-# LANGUAGE RecursiveDo #-}

module TCM where

import LocalPrelude
import Core
import Context

type TrackFreesT m = ReaderT Frees (ContextT m)
type TrackFrees    = TrackFreesT Identity

freshFree :: (Monad m) => (Int -> TrackFreesT m a) -> TrackFreesT m a
freshFree k = lift getFresh >>= \i -> local (i:) (k i)

freshFreeVar :: (Monad m) => (VTerm -> TrackFreesT m a) -> TrackFreesT m a
freshFreeVar k = freshFree (k . vvar)

toCTerm :: (Monad m) => Syntax -> TrackFreesT m CTerm
toCTerm = go [] where
  go :: (Monad m) => Env Name Int -> Syntax -> TrackFreesT m CTerm
  go vs  Star       = return CStar
  go vs (Pi  n a b) = freshFree $ \i -> CPi  n i <$> go vs a <*> go ((n, i) : vs) b
  go vs (Lam n t)   = freshFree $ \i -> CLam n i <$> go ((n, i) : vs) t
  go vs (App n ts)  = CApp <$> lift (Var <$> lookupContext n vs) <*> traverse (go vs) ts
  go vs (:?)        = return CMeta

--------------------

type TCMT m = StateT VCon (ContextT m)
type TCM    = TCMT Identity

runTCMT :: (Monad m) => TCMT m a -> m (Either String (a, (Int, DefEnv, MetaEnv)))
runTCMT a = runExceptT (runStateT (evalStateT a []) (0, [], (0, [])))

runTCM :: TCM a -> Either String (a, (Int, DefEnv, MetaEnv))
runTCM = runIdentity . runTCMT

evalTCM :: TCM a -> Either String (a, Env Name (VType, MetaKind))
evalTCM = (\(x, (_, _, (_, mks))) -> (x, mks)) <.> runTCM

trackFreesToTCM :: (Functor m) => TrackFreesT m a -> TCMT m a
trackFreesToTCM = readerToState (map fst)

withTyped :: (Monad m) => Name -> Int -> VType -> TCMT m a -> TCMT m a
withTyped n i a k = modify (++ [(i, (n, a))]) *> k <* modify init

nameVTypeOf :: (Monad m) => Head -> TCMT m (Name, VType)
nameVTypeOf h = do
  inas <- get
  (_, das, (_, mas)) <- lift get 
  lift $ case h of
    (Flex Def n)  -> n .> snd <$> lookupContext n das
    (Flex Meta n) -> n .> fst <$> lookupContext n mas
    (Var i)       -> lookupContext i inas

nameQTypeOf :: (Monad m) => Head -> TCMT m (Name, QType)
nameQTypeOf = second quote <.> nameVTypeOf

normVarTypes :: TCM ()
normVarTypes = modifyM $ traverse . secondM . secondM $ vnorm

normMetaTypes :: TCM ()
normMetaTypes = lift . readModifyM $ thirdM . secondM . traverse . secondM . firstM $ vnorm

newMetaKindBy :: (Monad m) => (Name -> Frees -> a) -> Name -> MetaKind -> VType -> TCMT m a
newMetaKindBy k n mk a = do
  inas <- get
  lift $ do
    (i, das, (m, mas)) <- get
    let nm = '?' : n ++ show m
    put (i, das, (m + 1, (nm, (craftVPis inas a, mk)) : mas))
    return . k nm $ map fst inas

newQMetaKind :: (Monad m) => Name -> MetaKind -> VType -> TCMT m QTerm
newQMetaKind = newMetaKindBy $ \n -> QApp (Flex Meta n) . map qvar

newVMetaKind :: (Monad m) => Name -> MetaKind -> VType -> TCMT m VTerm
newVMetaKind = newMetaKindBy $ foldl' (\f -> VApp f . vvar) . vmeta

newQGuarded :: (Monad m) => Equations -> QTerm -> VType -> TCMT m QTerm
newQGuarded es = newQMetaKind "" . Guarded es

newVGuarded :: (Monad m) => Equations -> QTerm -> VType -> TCMT m VTerm
newVGuarded es = newVMetaKind "" . Guarded es

newQCheck :: (Monad m) => VType -> Int -> CTerm -> VType -> TCMT m QTerm
newQCheck b l t a = do
  inas <- get
  newQMetaKind "" (Check b l (craftCLams (vconToCCon inas) t)) a

newQMeta :: (Monad m) => Name -> VType -> TCMT m QTerm
newQMeta n = newQMetaKind n Unknown

newVMeta :: (Monad m) => Name -> VType -> TCMT m VTerm
newVMeta n = newVMetaKind n Unknown

newTypedQMetaKind :: (Monad m) => MetaKind -> TCMT m (QTerm, VType)
newTypedQMetaKind mk = do
  a <- newVMeta "" VStar
  x <- newQMetaKind "" mk a
  return (x, a)

newTypedQCheck :: (Monad m) => VType -> Int -> CTerm -> TCMT m (QTerm, VType)
newTypedQCheck b l t = do
  inas <- get
  a <- newVMeta "" VStar
  x <- newQCheck b l t a
  return (x, a)

newTypedQMeta :: (Monad m) => TCMT m (QTerm, VType)
newTypedQMeta = newTypedQMetaKind Unknown

vguardedWhen :: (Monad m) => Equations -> QTerm -> VType -> TCMT m VTerm
vguardedWhen [] t a = lift $ eval t
vguardedWhen es t a = newVGuarded es t a

qguardedWhen :: (Monad m) => Equations -> QTerm -> VType -> TCMT m QTerm
qguardedWhen [] t a = return t
qguardedWhen es t a = traceShow t $ newQGuarded es t a

--------------------

solveConstraints :: TCM ()
solveConstraints = do
  (i, das, (m, mas)) <- lift get
  forM_ mas $ \(n, (a, mk)) -> case mk of
    Guarded es t -> do
      es' <- concat <$> traverse (uncurry vunify) es
      lift $ if null es' then qsolveMeta n t else updateMeta n (Guarded es' t)
    Check b l t  -> do
      nb <- lift $ vnorm b
      when (countVPis nb >= l) . localState [] $ mdo
        lift $ qsolveMeta n t'
        t' <- check t a
        return ()
    _            -> return ()

-- TODO: occurs check and friends.
tryMiller :: QTerm -> QTerm -> MaybeT TCM ()
tryMiller (QApp (Flex Meta n) ts) s | Just lvs <- traverse unQVar ts = do
  True <- lift2 $ checkIsSolvable n
  lift $ freeVars s `isUniqueSublistOf` lvs ?> do
    inas <- traverse (\i -> i .> nameQTypeOf (Var i)) lvs
    lift $ qsolveMeta n (craftQLams inas s)
    normMetaTypes
    solveConstraints
tryMiller  t                      s = mzero

tryMillerBoth :: QTerm -> QTerm -> MaybeT TCM ()
tryMillerBoth t s = tryMiller t s <|> tryMiller s t

tryUnifyChilds :: Bool -> QSpine -> QSpine -> MaybeT TCM Equations
tryUnifyChilds b ts ss = 
  maybe (b ?> lift3 (throwE "different number of arguments"))
        (lift . (concat <.> sequence))
        (zipWithEq qunify ts ss)

-- TODO: intersections stuff.
tryFlexAny :: QTerm -> QTerm -> MaybeT TCM ()
tryFlexAny t@(QApp (Flex f n) ts) s@(QApp (Flex g m) ss) =
  n == m ?> do
    [] <- tryUnifyChilds (all isForeverNeutral (ts ++ ss)) ts ss
    return ()
tryFlexAny t                      s                      = tryMillerBoth t s

tryQAppUnify :: QTerm -> QTerm -> MaybeT TCM Equations
tryQAppUnify t@(QApp (Var i) ts) s@(QApp (Var j) ss) =
  if i == j
    then tryUnifyChilds True ts ss
    else lift3 $ throwE "different variables in heads"
tryQAppUnify t                   s                   = [] <$ tryFlexAny t s

tryEtaExpandUnifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations)
                      -> VTerm -> VTerm -> MaybeT TCM Equations
tryEtaExpandUnifyWith cont t@(VLam n i a k) s = lift $ unifyWith cont t (etaExpand n i a s)
tryEtaExpandUnifyWith cont _                _ = mzero

tryEtaExpandUnifyWithBoth :: (VTerm -> VTerm -> MaybeT TCM Equations)
                          -> VTerm -> VTerm -> MaybeT TCM Equations
tryEtaExpandUnifyWithBoth cont t s =  tryEtaExpandUnifyWith cont t s
                                  <|> tryEtaExpandUnifyWith cont s t

-- This really should be type-directed.
unifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations) -> VTerm -> VTerm -> TCM Equations
unifyWith cont  VStar            VStar           = return []
unifyWith cont (VPi  n i a1 b1) (VPi  m j a2 b2) = do
  es <- unifyWith cont a1 a2
  (es ++) <.> withTyped n i a1 $ do
    gv <- vguardedWhen es (qvar i) a2
    nb1 <- lift $ vnorm (b1 (vvar i))
    nb2 <- lift $ vnorm (b2  gv)
    unifyWith cont nb1 nb2
unifyWith cont (VLam n i a1 k1) (VLam m j a2 k2) =
  withTyped n i a1 $ unifyWith cont (k1 (vvar i)) (k2 (vvar i))
unifyWith cont  t                s               =
  fromMaybeT (return [(t, s)]) $ tryEtaExpandUnifyWithBoth cont t s <|> cont t s

evalUnify :: QTerm -> QTerm -> TCM Equations
evalUnify t s = unifyWith (\_ _ -> mzero) <$> lift (eval t) <&> lift (eval s)

qunify :: QTerm -> QTerm -> TCM Equations
qunify t s = fromMaybeT (evalUnify t s) $ tryQAppUnify t s

tryQuoteUnify :: VTerm -> VTerm -> MaybeT TCM Equations
tryQuoteUnify t s = tryQAppUnify (quote t) (quote s)

vunify :: VTerm -> VTerm -> TCM Equations
vunify = unifyWith tryQuoteUnify

--------------------

unify :: VTerm -> VTerm -> TCM Equations
unify t s = vunify t s <* normVarTypes

infer :: CTerm -> TCM (QTerm, VType)
infer    CStar        = return (QStar, VStar)
infer   (CPi n i a b) = do
  (na, ena) <- checkEval a VStar
  withTyped n i ena $ do
    nb <- check b VStar
    return (QPi n i na nb, VStar)
infer   (CLam n i t)  = lift2 $ throwE "lambdas are non-inferrable"
infer t@(CApp h ts)   = do
  b <- snd <$> nameVTypeOf h
  let l = length ts
  if countVPis b < l
    then newTypedQCheck b l t
    else saturate (QApp h) b ts
infer    CMeta        = newTypedQMeta

saturate :: (QSpine -> QTerm) -> VType -> CSpine -> TCM (QTerm, VType)
saturate k  a             []    = return (k [], a)
saturate k (VPi n i a b) (x:xs) = checkEval x a >>= \(nx, enx) -> saturate (k . (nx:)) (b enx) xs

check :: CTerm -> VType -> TCM QTerm
check (CLam n i t) (VPi m j a b) = QLam n i (quote a) <$> withTyped n i a (check t (b (vvar i)))
check  t            a            = do
  (t', a') <- infer t
  es <- unify a' a
  qguardedWhen es t' a

checkEval :: CTerm -> VType -> TCM (QTerm, VTerm)
checkEval t a = do
  ct   <- check t a
  ect  <- lift $ eval ct
  return (quote ect, ect)

typecheck :: CTerm -> CType -> TCM (QTerm, QTerm)
typecheck t a = do
  (qeca, eca) <- checkEval a VStar
  ect <- check t eca -- >>>= qnorm
  nqeca <- lift $ qnorm qeca
  return (ect, nqeca)

stypecheck :: Syntax -> Syntax -> TCM (Syntax, Syntax)
stypecheck t a = do
  ca <- trackFreesToTCM $ toCTerm a
  ct <- trackFreesToTCM $ toCTerm t
  (toSyntax *** toSyntax) <$> typecheck ct ca
