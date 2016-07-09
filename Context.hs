module Context where

import LocalPrelude
import Core

type DefEnv     = Env Int (VTerm, VType)
type MetaEnv    = (Int, Env Int (VType, MetaKind))
type ContextT m = StateT (Int, DefEnv, MetaEnv) (ExceptT String m)

lookupContext :: (Monad m, Eq a, Show a) => a -> Env a b -> ContextT m b
lookupContext x = maybe (lift . throwE $ "panic: " ++ show x ++ " is not in scope") return . lookup x

getFresh :: (Monad m) => ContextT m Int
getFresh = do
  (i, das, mmas) <- get
  put (i + 1, das, mmas)
  return i

fresh :: (Monad m) => (Int -> ContextT m a) -> ContextT m a
fresh k = getFresh >>= k

checkIsSolvable :: (Monad m) => Int -> ContextT m Bool
checkIsSolvable i = do
  (_, _, (_, mas)) <- get
  isSolvable . snd <$> lookupContext i mas

updateMeta :: (Monad m) => Int -> MetaKind -> ContextT m ()
updateMeta j mk = modify $
  \(i, das, (m, mas)) -> (i, das, (m, mapup j (second (const mk)) mas))

vsolveMeta :: (Monad m) => Int -> VTerm -> ContextT m ()
vsolveMeta i = updateMeta i . Solution

qsolveMeta :: (Monad m) => Int -> QTerm -> ContextT m ()
qsolveMeta i = eval >=> vsolveMeta i

-- Such a mess.
getLookup :: (Monad m) => ContextT m (Env Int VTerm -> Head -> Maybe VTerm)
getLookup = do
  (_, das, (_, mas)) <- get
  return $ \vs h -> case h of
    (Meta (Entry n i)) -> maybe (error $ "panic: meta " ++ n ++ " is not in scope")
                                (tryGetSolution . snd)
                                (lookup i mas)
    (Var  (Entry n i)) -> lookup i vs

eval :: (Monad m) => QTerm -> ContextT m VTerm
eval t = flip pureEval t <$> getLookup

qnorm :: (Monad m) => QTerm -> ContextT m QTerm
qnorm = quote <.> eval

vnorm :: (Monad m) => VTerm -> ContextT m VTerm
vnorm = eval . quote

toCTerm :: (Monad m) => Syntax -> ContextT m CTerm
toCTerm = go [] where
  go :: (Monad m) => Env String Int -> Syntax -> ContextT m CTerm
  go vs  Star       = return CStar
  go vs (Pi  n a b) = fresh $ \i -> CPi  (Entry n i) <$> go vs a <*> go ((n, i) : vs) b
  go vs (Lam n t)   = fresh $ \i -> CLam (Entry n i) <$> go ((n, i) : vs) t
  go vs (App n ts)  = CApp . Var . Entry n <$> lookupContext n vs <*> traverse (go vs) ts
  go vs (:?)        = return CMeta
