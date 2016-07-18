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

throwTCM :: (Monad m) => String -> TCMT m a
throwTCM = lift2 . throwE

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

newMetaKindBy :: (Monad m) => (Entry -> [Entry] -> a) -> String -> VType -> MetaKind -> TCMT m a
newMetaKindBy k n a mk = do
  inas <- get
  lift $ do
    (i, das, (m, mas)) <- get
    put (i, das, (m + 1, mas ++ [(m, (vcraft VPi inas a, mk))]))
    return . k (Entry n m) $ map (\(i, (n, _)) -> Entry n i) inas

newQMetaKind :: (Monad m) => String -> VType -> MetaKind -> TCMT m QTerm
newQMetaKind = newMetaKindBy $ \e -> QApp (Meta e) . map qvar

newVMetaKind :: (Monad m) => String -> VType -> MetaKind -> TCMT m VTerm
newVMetaKind = newMetaKindBy $ foldl' (\f -> VApp f . vvar) . vmeta

craftGuarded :: (Monad m) => Equations -> QTerm -> TCMT m MetaKind
craftGuarded es t = (\inas -> Guarded es (qcraft (\e _ -> QLam e) (vconToQCon inas) t)) <$> get

newQGuarded :: (Monad m) => Equations -> VType -> QTerm -> TCMT m QTerm
newQGuarded es a = craftGuarded es >=> newQMetaKind "" a

newVGuarded :: (Monad m) => Equations -> VType -> QTerm -> TCMT m VTerm
newVGuarded es a = craftGuarded es >=> newVMetaKind "" a

newQCheck :: (Monad m) => VType -> Int -> CTerm -> VType -> TCMT m QTerm
newQCheck b l t a = do
  inas <- get
  newQMetaKind "" a $ Check b l (craftCLams (vconToCCon inas) t)

newQMeta :: (Monad m) => String -> VType -> TCMT m QTerm
newQMeta n a = newQMetaKind n a Unknown

newVMeta :: (Monad m) => String -> VType -> TCMT m VTerm
newVMeta n a = newVMetaKind n a Unknown

newVTypeMeta :: (Monad m) => TCMT m VType
newVTypeMeta = newVMeta "" VStar

newTypedQMetaKind :: (Monad m) => MetaKind -> TCMT m (QTerm, VType)
newTypedQMetaKind mk = do
  a <- newVTypeMeta
  x <- newQMetaKind "" a mk
  return (x, a)

newTypedQCheck :: (Monad m) => VType -> Int -> CTerm -> TCMT m (QTerm, VType)
newTypedQCheck b l t = do
  a <- newVTypeMeta
  x <- newQCheck b l t a
  return (x, a)

newTypedQMeta :: (Monad m) => TCMT m (QTerm, VType)
newTypedQMeta = newTypedQMetaKind Unknown

vguardedWhen :: (Monad m) => Equations -> VType -> QTerm -> TCMT m VTerm
vguardedWhen [] a t = lift $ eval t
vguardedWhen es a t = newVGuarded es a t

qguardedWhen :: (Monad m) => Equations -> VType -> QTerm -> TCMT m QTerm
qguardedWhen [] a t = return t
qguardedWhen es a t = traceShow t $ newQGuarded es a t

--------------------

solveConstraints :: TCM ()
solveConstraints = do
  (i, das, (m, mas)) <- lift get
  forM_ mas $ \(j, (a, mk)) -> case mk of
    Guarded es t -> do
      es' <- concat <.> forM es $
        \(a, x, y) -> unify a <$> lift (vnorm x) <&> lift (vnorm y)
      lift $ if null es' then qsolveMeta j t else updateMeta j (Guarded es' t)
    Check b l t  -> do
      nb <- lift $ vnorm b
      when (countVPis nb >= l) . localState [] $ mdo
        lift $ qsolveMeta j t'
        t' <- check t a
        return ()
    Solution t   -> lift $ vnorm t >>= vsolveMeta j
    _            -> return ()

-- TODO: occurs check and friends.
tryMiller :: QTerm -> QTerm -> MaybeT TCM ()
tryMiller t@(QApp (Meta (Entry _ i)) ts) s | Just lvs <- traverse unQVar ts = do
  True <- lift2 $ checkIsSolvable i
  lift $ case freeVars s `tryIsUniqueSublistOf` map getId lvs of
    Nothing -> throwTCM $ show t ++ " and " ++ show s ++ " can't be unified"
    Just b  -> b ?> do
      inas <- traverse (\e@(Entry n i) -> i .> nameQTypeOf (Var e)) lvs
      lift $ qsolveMeta i (qcraft (\e _ -> QLam e) inas s)
      normMetaTypes
      solveConstraints
      normVarTypes
tryMiller  t                             s = mzero

tryMillerBoth :: QTerm -> QTerm -> MaybeT TCM ()
tryMillerBoth t s = tryMiller t s <|> tryMiller s t

tryUnifyChilds :: Bool -> Head -> QSpine -> QSpine -> MaybeT TCM Equations
tryUnifyChilds c h ts ss =
  lift (nameVTypeOf h) >>= \(_, a) -> lift2 (vnorm a) >>= \na -> go c na ts ss where
  go c a   []     []    = return []
  go c ab (t:ts) (s:ss) = case ab of
    -- What if `t =?= s` results in unsolved constraints? That `b et` looks troubling.
    (VPi _ a b) -> lift2 (eval t) >>= \et -> (++) <$> lift (qunify a t s) <*> go c (b et) ts ss
    _           -> lift $ throwTCM "panic: something bad happened"
  go c a   ts     ss    = c ?> lift (throwTCM "different number of arguments")

-- TODO: intersections stuff.
tryFlexAny :: QTerm -> QTerm -> MaybeT TCM ()
tryFlexAny t@(QApp h@(Meta (Entry _ i)) ts) s@(QApp (Meta (Entry _ j)) ss) =
  i == j ?> do
    [] <- tryUnifyChilds (all isForeverNeutral (ts ++ ss)) h ts ss
    return ()
tryFlexAny t                                s                              = tryMillerBoth t s

tryQAppUnify :: QTerm -> QTerm -> MaybeT TCM Equations
tryQAppUnify t@(QApp h@(Var (Entry _ i)) ts) s@(QApp (Var (Entry _ j)) ss) =
  if i == j
    then tryUnifyChilds True h ts ss
    else lift $ throwTCM "different variables in heads"
tryQAppUnify t                               s                             = [] <$ tryFlexAny t s

unifyWith :: (VTerm -> VTerm -> MaybeT TCM Equations) -> VType -> VTerm -> VTerm -> TCM Equations
unifyWith cont  VStar       VStar          VStar         = return []
unifyWith cont  VStar      (VPi  e a1 b1) (VPi  _ a2 b2) = do
  es <- unifyWith cont VStar a1 a2
  (es ++) <.> withTyped e a1 $ do
    gv <- vguardedWhen es a2 (qvar e)
    nb1 <- lift $ vnorm (b1 (vvar e))
    nb2 <- lift $ vnorm (b2  gv)
    unifyWith cont VStar nb1 nb2
unifyWith cont (VPi e a b)  t1             t2            =
  withTyped e a $ unifyWith cont (b (vvar e)) (k1 (vvar e)) (k2 (vvar e)) where
    VLam _ k1 = etaExpandUnless e t1
    VLam _ k2 = etaExpandUnless e t2
unifyWith cont  a           t1             t2            =
  fromMaybeT (return [(a, t1, t2)]) $ cont t1 t2

evalUnify :: VType -> QTerm -> QTerm -> TCM Equations
evalUnify a t s = unifyWith (\_ _ -> mzero) a <$> lift (eval t) <&> lift (eval s)

qunify :: VType -> QTerm -> QTerm -> TCM Equations
qunify a t s = fromMaybeT (evalUnify a t s) $ tryQAppUnify t s

tryQuoteUnify :: VTerm -> VTerm -> MaybeT TCM Equations
tryQuoteUnify t s = tryQAppUnify (quote t) (quote s)

unify :: VType -> VTerm -> VTerm -> TCM Equations
unify a t s = unifyWith tryQuoteUnify a t s

infer :: CTerm -> TCM (QTerm, VType)
infer    CStar      = return (QStar, VStar)
infer   (CPi e a b) = do
  (na, ena) <- checkEval a VStar
  withTyped e ena $ do
    nb <- check b VStar
    return (QPi e na nb, VStar)
infer   (CLam e t)  = throwTCM "panic: how did you get here?"
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
check   (CLam  e          t) (VPi _ a b) = QLam e <$> withTyped e a (check t (b (vvar e)))
check l@(CLam (Entry n _) t)  c          = case quote c of
  QApp (Meta _) ts -> do
    i <- lift $ getFresh
    c' <- snd <$> checkEval (CPi (Entry n i) CMeta CMeta) VStar
    t' <- check l c'
    nc' <- lift $ vnorm c'
    es <- unify VStar nc' c
    qguardedWhen es c t'
  _                -> throwTCM "mismatch"
check t                       a          = do
  (t', a') <- infer t
  es <- unify VStar a' a
  qguardedWhen es a t'

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

stypecheck :: Syntax -> Syntax -> TCM (QTerm, QTerm)
stypecheck t a = typecheck <$> lift (toCTerm t) <&> lift (toCTerm a)
