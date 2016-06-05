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

-- Unification works in this context indeed, but typechecking
-- should run in `StateT Con (ContextT m)` to avoid that `vnorm` in `typeOf`.
type TCMT m = ReaderT Con (ContextT m)
type TCM    = TCMT Identity

runTCMT :: (Monad m) => TCMT m a -> m (Either String (a, (Int, DefEnv, MetaEnv)))
runTCMT a = runExceptT (runStateT (runReaderT a []) (0, [], (0, [])))

runTCM :: TCM a -> Either String (a, (Int, DefEnv, MetaEnv))
runTCM = runIdentity . runTCMT

evalTCM :: TCM a -> Either String (a, Env Name (VType, MetaKind))
evalTCM = (\(x, (_, _, (_, mks))) -> (x, mks)) <.> runTCM

trackFreesToTCM :: TrackFreesT m a -> TCMT m a
trackFreesToTCM = withReaderT (map fst)

regTyped :: (Monad m) => Name -> VType -> Int -> TCMT m a -> TCMT m a
regTyped n a i k = local ((i, (n, a)) :) k

freshTyped :: (Monad m) => Name -> VType -> (Int -> TCMT m a) -> TCMT m a
freshTyped n a k = lift getFresh >>= \i -> regTyped n a i (k i)

freshTypedVar :: (Monad m) => Name -> VType -> (VTerm -> TCMT m a) -> TCMT m a
freshTypedVar n a k = freshTyped n a (k . vvar)

typeOf :: (Monad m) => Head -> TCMT m VType
typeOf h = vnorm =<<< do
  inas <- ask
  (_, das, (_, mas)) <- lift get 
  lift $ case h of
    (Flex Def n)  -> snd <$> lookupContext n das
    (Flex Meta n) -> fst <$> lookupContext n mas
    (Var i)       -> snd <$> lookupContext i inas

-- In a future.
-- vnormTypes :: TCM ()
-- vnormTypes = modifyM $ traverse (secondM (secondM vnorm))

newMetaKindBy :: (Monad m) => (Name -> Frees -> a) -> Name -> MetaKind -> VType -> TCMT m a
newMetaKindBy k n mk a = do
  inas <- ask
  lift $ do
    (i, das, (m, mas)) <- get
    let nm = '?' : n ++ show m
    b <- craftVPis inas a
    put (i, das, (m + 1, (nm, (b, mk)) : mas))
    return . k nm $ map fst inas

newQMetaKind :: (Monad m) => Name -> MetaKind -> VType -> TCMT m QTerm
newQMetaKind = newMetaKindBy $ \n -> QApp (Flex Meta n) . map qvar

newVMetaKind :: (Monad m) => Name -> MetaKind -> VType -> TCMT m VTerm
newVMetaKind = newMetaKindBy $ foldl' (\f -> VApp f . vvar) . vmeta

newQGuarded :: (Monad m) => Equations -> QTerm -> VType -> TCMT m QTerm
newQGuarded es = newQMetaKind "" . Guarded es

newVGuarded :: (Monad m) => Equations -> QTerm -> VType -> TCMT m VTerm
newVGuarded es = newVMetaKind "" . Guarded es

newQCheck :: (Monad m) => CTerm -> VType -> TCMT m QTerm
newQCheck = newQMetaKind "" . Check

newVCheck :: (Monad m) => CTerm -> VType -> TCMT m VTerm
newVCheck = newVMetaKind "" . Check

newQMeta :: (Monad m) => Name -> VType -> TCMT m QTerm
newQMeta n = newQMetaKind n Unknown

newVMeta :: (Monad m) => Name -> VType -> TCMT m VTerm
newVMeta n = newVMetaKind n Unknown

newTypedQMetaKind :: (Monad m) => MetaKind -> TCMT m (QTerm, VType)
newTypedQMetaKind mk = do
  a <- newVMeta "" VStar
  x <- newQMetaKind "" mk a
  return (x, a)

newTypedQCheck :: (Monad m) => CTerm -> TCMT m (QTerm, VType)
newTypedQCheck = newTypedQMetaKind . Check

newTypedQMeta :: (Monad m) => TCMT m (QTerm, VType)
newTypedQMeta = newTypedQMetaKind Unknown

vguardedWhen :: (Monad m) => Equations -> QTerm -> VType -> TCMT m VTerm
vguardedWhen [] t a = lift $ eval t
vguardedWhen es t a = newVGuarded es t a

qguardedWhen :: (Monad m) => Equations -> QTerm -> VType -> TCMT m QTerm
qguardedWhen [] t a = return t
qguardedWhen es t a = newQGuarded es t a

--------------------

-- TODO: metas must form a DAG.
tryMiller :: QTerm -> QTerm -> MaybeT TCM ()
tryMiller (QApp (Flex Meta n) ts) s | Just lvs <- traverse unQVar ts = do
  True <- lift2 $ checkIsSolvable n
  lift $ freeVars s `isUniqueSublistOf` lvs ?>
    (traverse (\i -> typeOf (Var i) >>>= (,) i <.> quote) lvs >>>=
      qsolveMeta n . flip craftQLamsFrom s)
tryMiller  t                      s = mzero

tryMillerBoth :: QTerm -> QTerm -> MaybeT TCM ()
tryMillerBoth t s = tryMiller t s <|> tryMiller s t

tryUnifyChildsOf :: QTerm -> QTerm -> MaybeT TCM Equations
tryUnifyChildsOf t@(QApp _ ts) s@(QApp _ ss) = lift $
  maybe (if all isForeverNeutral (ts ++ ss) -- We can do better.
           then lift2 $ throwE "different number of arguments"
           else mzero)
        (concat <.> sequence)
        (zipWithEq qunify ts ss)

-- TODO: intersections stuff.
tryFlexAny :: QTerm -> QTerm -> MaybeT TCM ()
tryFlexAny t@(QApp (Flex f n) ts) s@(QApp (Flex g m) ss) =
  n == m ?> do
    [] <- tryUnifyChildsOf t s
    return ()
tryFlexAny t                      s                      = tryMillerBoth t s

tryQAppUnify :: QTerm -> QTerm -> MaybeT TCM Equations
tryQAppUnify t@(QApp (Var i) ts) s@(QApp (Var j) ss) =
  if i /= j
    then lift . lift2 $ throwE "different variables in heads"
    else tryUnifyChildsOf t s
tryQAppUnify t                   s                   = [] <$ tryFlexAny t s

tryEtaExpandUnifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations)
                      -> VTerm -> VTerm -> MaybeT TCM Equations
tryEtaExpandUnifyWith cont t@(VLam n a k) s = lift $ unifyWith cont t (etaExpand n a s)
tryEtaExpandUnifyWith cont _              _ = mzero

tryEtaExpandUnifyWithBoth :: (VTerm -> VTerm -> MaybeT TCM Equations)
                          -> VTerm -> VTerm -> MaybeT TCM Equations
tryEtaExpandUnifyWithBoth cont t s =  tryEtaExpandUnifyWith cont t s
                                  <|> tryEtaExpandUnifyWith cont s t

-- This really should be type-directed.
unifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations) -> VTerm -> VTerm -> TCM Equations
unifyWith cont  VStar          VStar         = return []
unifyWith cont (VPi  n a1 b1) (VPi  m a2 b2) = do
  es <- unifyWith cont a1 a2
  (es ++) <.> freshTyped n a1 $ \i -> do
    gv <- vguardedWhen es (qvar i) a2
    unifyWith cont (b1 (vvar i)) (b2 gv)
unifyWith cont (VLam n a1 k1) (VLam m a2 k2) =
  freshTypedVar n a1 $ \v -> unifyWith cont (k1 v) (k2 v)
unifyWith cont  t              s             =
  fromMaybeT (return [(t, s)]) $ tryEtaExpandUnifyWithBoth cont t s <|> cont t s

evalUnify :: QTerm -> QTerm -> TCM Equations
evalUnify t s = unifyWith (\_ _ -> mzero) <$> lift (eval t) <&> lift (eval s)

qunify :: QTerm -> QTerm -> TCM Equations
qunify t s = fromMaybeT (evalUnify t s) $ tryQAppUnify t s

tryQuoteUnify :: VTerm -> VTerm -> MaybeT TCM Equations
tryQuoteUnify t s = tryQAppUnify <$> lift2 (quote t) <&> lift2 (quote s)

vunify :: VTerm -> VTerm -> TCM Equations
vunify = unifyWith tryQuoteUnify

--------------------

-- A guard/check can't be resolved during unification/checking,
-- because it's not in scope there, so we're safe.
-- This is disgusting.
{-solveConstraints :: TCM ()
solveConstraints = do
  (i, das, (m, mas)) <- lift get
  forM_ mas $ \(n, (a, mk)) -> case mk of
    Guarded es t -> do
      es' <- concat <$> traverse (uncurry vunify) es
      lift $ if null es'
         then qsolveMeta n t
         else updateMeta n (Guarded es' t)
    Check t      -> do
      na <- lift $ vnorm a
      tc <- tryCheck t a
      lift $ case tc of
        Right t' -> qsolveMeta n t'
        Left _   -> updateMeta n (Check t) -- na
    _            -> return ()-}

unify :: VTerm -> VTerm -> TCM Equations
unify t s = vunify t s -- <* solveConstraints -- <* vnormTypes

infer :: CTerm -> TCM (QTerm, VType)
infer    CStar        = return (QStar, VStar)
infer   (CPi n i a b) = do
  (na, ena) <- checkEval a VStar
  regTyped n ena i $ do
    nb <- check b VStar
    return (QPi n i na nb, VStar)
infer   (CLam n i t)  = lift2 $ throwE "lambdas are non-inferrable"
infer t@(CApp h ts)   = do
  b <- typeOf h
  pis <- lift $ countVPis b
  if pis < length ts
    then newTypedQCheck t
    else saturate (QApp h) b ts
infer    CMeta        = newTypedQMeta

saturate :: (QSpine -> QTerm) -> VType -> CSpine -> TCM (QTerm, VType)
saturate k  a           []    = return (k [], a)
saturate k (VPi n a b) (x:xs) = checkEval x a >>= \(nx, enx) -> saturate (k . (nx:)) (b enx) xs

check :: CTerm -> VType -> TCM QTerm
check (CLam n i t) (VPi m a b) =
  QLam n i <$> lift (quote a) <*> regTyped n a i (check t (b (vvar i)))
check  t            a          = do
  (t', a') <- infer t
  es <- unify a' a
  qguardedWhen es t' a

checkEval :: CTerm -> VType -> TCM (QTerm, VTerm)
checkEval t a = do
  ct   <- check t a
  ect  <- lift $ eval ct
  qect <- lift $ quote ect
  return (qect, ect)

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
