{-# LANGUAGE RecursiveDo #-}

module TCM where

import LocalPrelude
import Core
import Context

type TCMT m = StateT VCon (ContextT m)
type TCM    = TCMT Identity

runTCMT :: (Monad m) => TCMT m a -> m (Either String (a, (Int, DefEnv, MetaEnv)))
runTCMT a = runExceptT (runStateT (evalStateT a []) (0, [], (0, [])))

runTCM :: TCM a -> Either String (a, (Int, DefEnv, MetaEnv))
runTCM = runIdentity . runTCMT

evalTCM :: TCM a -> Either String (a, Env Int (VType, MetaKind))
evalTCM = (\(x, (_, _, (_, mks))) -> (x, mks)) <.> runTCM

withTyped :: (Monad m) => Entry -> VType -> TCMT m a -> TCMT m a
withTyped (Entry n i) a k = modify (++ [(i, (n, a))]) *> k <* modify init

nameVTypeOf :: (Monad m) => Head -> TCMT m (String, VType)
nameVTypeOf h = do
  inas <- get
  (_, das, (_, mas)) <- lift get 
  lift $ case h of
    (Meta (Entry n i)) -> n .> fst <$> lookupContext i mas
    (Var  (Entry n i)) -> lookupContext i inas

nameQTypeOf :: (Monad m) => Head -> TCMT m (String, QType)
nameQTypeOf = second quote <.> nameVTypeOf

normVarTypes :: TCM ()
normVarTypes = modifyM $ traverse . secondM . secondM $ vnorm

normMetaTypes :: TCM ()
normMetaTypes = lift . readModifyM $ thirdM . secondM . traverse . secondM . firstM $ vnorm

newMetaKindBy :: (Monad m) => (Entry -> [Entry] -> a) -> String -> MetaKind -> VType -> TCMT m a
newMetaKindBy k n mk a = do
  inas <- get
  lift $ do
    (i, das, (m, mas)) <- get
    put (i, das, (m + 1, (m, (vcraft VPi inas a, mk)) : mas))
    return . k (Entry n m) $ map (\(i, (n, _)) -> Entry n i) inas

newQMetaKind :: (Monad m) => String -> MetaKind -> VType -> TCMT m QTerm
newQMetaKind = newMetaKindBy $ \e -> QApp (Meta e) . map qvar

newVMetaKind :: (Monad m) => String -> MetaKind -> VType -> TCMT m VTerm
newVMetaKind = newMetaKindBy $ foldl' (\f -> VApp f . vvar) . vmeta

craftGuarded :: (Monad m) => Equations -> QTerm -> TCMT m MetaKind
craftGuarded es t = (\inas -> Guarded es (qcraft QLam (vconToQCon inas) t)) <$> get

newQGuarded :: (Monad m) => Equations -> QTerm -> VType -> TCMT m QTerm
newQGuarded es t a = craftGuarded es t >>= \t' -> newQMetaKind "" t' a

newVGuarded :: (Monad m) => Equations -> QTerm -> VType -> TCMT m VTerm
newVGuarded es t a = craftGuarded es t >>= \t' -> newVMetaKind "" t' a

newQCheck :: (Monad m) => VType -> Int -> CTerm -> VType -> TCMT m QTerm
newQCheck b l t a = do
  inas <- get
  newQMetaKind "" (Check b l (craftCLams (vconToCCon inas) t)) a

newQMeta :: (Monad m) => String -> VType -> TCMT m QTerm
newQMeta n = newQMetaKind n Unknown

newVMeta :: (Monad m) => String -> VType -> TCMT m VTerm
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
  forM_ mas $ \(j, (a, mk)) -> case mk of
    Guarded es t -> traceShow es $ do
      es' <- concat <$> traverse (\(x, y) -> vunify <$> lift (vnorm x) <&> lift (vnorm y)) es
      lift $ if null es' then qsolveMeta j t else updateMeta j (Guarded es' t)
    Check b l t  -> do
      nb <- lift $ vnorm b
      when (countVPis nb >= l) . localState [] $ mdo
        lift $ qsolveMeta j t'
        t' <- check t a
        return ()
    _            -> return ()

-- TODO: occurs check and friends.
-- TODO: if `freeVars s` is not a sublist of `lvs`, we have an error.
tryMiller :: QTerm -> QTerm -> MaybeT TCM ()
tryMiller (QApp (Meta (Entry _ i)) ts) s | Just lvs <- traverse unQVar ts = do
  True <- lift2 $ checkIsSolvable i
  lift $ freeVars s `isUniqueSublistOf` map getId lvs ?> do
    inas <- traverse (\e@(Entry n i) -> i .> nameQTypeOf (Var e)) lvs
    lift $ qsolveMeta i (qcraft QLam inas s)
    normMetaTypes
    solveConstraints
tryMiller  t                           s = mzero

tryMillerBoth :: QTerm -> QTerm -> MaybeT TCM ()
tryMillerBoth t s = tryMiller t s <|> tryMiller s t

tryUnifyChilds :: Bool -> QSpine -> QSpine -> MaybeT TCM Equations
tryUnifyChilds b ts ss = 
  maybe (b ?> lift3 (throwE "different number of arguments"))
        (lift . (concat <.> sequence))
        (zipWithEq qunify ts ss)

-- TODO: intersections stuff.
tryFlexAny :: QTerm -> QTerm -> MaybeT TCM ()
tryFlexAny t@(QApp (Meta e) ts) s@(QApp (Meta f) ss) =
  e == f ?> do
    [] <- tryUnifyChilds (all isForeverNeutral (ts ++ ss)) ts ss
    return ()
tryFlexAny t                    s                    = tryMillerBoth t s

tryQAppUnify :: QTerm -> QTerm -> MaybeT TCM Equations
tryQAppUnify t@(QApp (Var i) ts) s@(QApp (Var j) ss) =
  if i == j
    then tryUnifyChilds True ts ss
    else lift3 $ throwE "different variables in heads"
tryQAppUnify t                   s                   = [] <$ tryFlexAny t s

tryEtaExpandUnifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations)
                      -> VTerm -> VTerm -> MaybeT TCM Equations
tryEtaExpandUnifyWith cont t@(VLam e a k) s = lift $ unifyWith cont t (etaExpand e a s)
tryEtaExpandUnifyWith cont _              _ = mzero

tryEtaExpandUnifyWithBoth :: (VTerm -> VTerm -> MaybeT TCM Equations)
                          -> VTerm -> VTerm -> MaybeT TCM Equations
tryEtaExpandUnifyWithBoth cont t s =  tryEtaExpandUnifyWith cont t s
                                  <|> tryEtaExpandUnifyWith cont s t

-- This really should be type-directed.
unifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations) -> VTerm -> VTerm -> TCM Equations
unifyWith cont  VStar          VStar         = return []
unifyWith cont (VPi  e a1 b1) (VPi  _ a2 b2) = do
  es <- unifyWith cont a1 a2
  (es ++) <.> withTyped e a1 $ do
    gv <- vguardedWhen es (qvar e) a2
    nb1 <- lift $ vnorm (b1 (vvar e))
    nb2 <- lift $ vnorm (b2  gv)
    unifyWith cont nb1 nb2
    -- unifyWith cont (b1 (vvar e)) (b2 gv)
unifyWith cont (VLam e a1 k1) (VLam _ a2 k2) =
  withTyped e a1 $ unifyWith cont (k1 (vvar e)) (k2 (vvar e))
unifyWith cont  t              s             =
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
infer    CStar      = return (QStar, VStar)
infer   (CPi e a b) = do
  (na, ena) <- checkEval a VStar
  withTyped e ena $ do
    nb <- check b VStar
    return (QPi e na nb, VStar)
infer   (CLam e t)  = lift2 $ throwE "lambdas are non-inferrable"
infer t@(CApp h ts) = do
  b <- snd <$> nameVTypeOf h
  let l = length ts
  if countVPis b < l
    then newTypedQCheck b l t
    else saturate (QApp h) b ts
infer    CMeta      = newTypedQMeta

saturate :: (QSpine -> QTerm) -> VType -> CSpine -> TCM (QTerm, VType)
saturate k  a           []    = return (k [], a)
saturate k (VPi e a b) (x:xs) = checkEval x a >>= \(nx, enx) -> saturate (k . (nx:)) (b enx) xs

check :: CTerm -> VType -> TCM QTerm
check (CLam e t) (VPi _ a b) = QLam e (quote a) <$> withTyped e a (check t (b (vvar e)))
check  t          a          = do
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
  solveConstraints
  ect <- check t eca
  solveConstraints
  nect  <- lift $ qnorm ect
  nqeca <- lift $ qnorm qeca
  return (nect, nqeca)

stypecheck :: Syntax -> Syntax -> TCM (Syntax, Syntax)
stypecheck t a =
  (qtermToSyntax *** qtermToSyntax) <$> (typecheck <$> lift (toCTerm t) <&> lift (toCTerm a))
