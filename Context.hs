module Context where

import LocalPrelude
import Core

type DefEnv     = Env Name (VTerm, VType)
type MetaEnv    = (Int, Env Name (VType, MetaKind))
type ContextT m = StateT (Int, DefEnv, MetaEnv) (ExceptT String m)

lookupContext :: (Monad m, Eq a, Show a) => a -> Env a b -> ContextT m b
lookupContext x = maybe (lift . throwE $ "panic: " ++ show x ++ " is not found") return . lookup x

getFresh :: (Monad m) => ContextT m Int
getFresh = do
  (i, das, mmas) <- get
  put (i + 1, das, mmas)
  return i

fresh :: (Monad m) => (Int -> ContextT m a) -> ContextT m a
fresh k = getFresh >>= k

freshVar :: (Monad m) => (VTerm -> ContextT m a) -> ContextT m a
freshVar k = fresh (k . vvar)

checkIsSolvable :: (Monad m) => Name -> ContextT m Bool
checkIsSolvable n = do
  (_, _, (_, mas)) <- get
  isSolvable . snd <$> lookupContext n mas

updateMeta :: (Monad m) => Name -> MetaKind -> ContextT m ()
updateMeta n mk = modify $
  \(i, das, (m, mas)) -> (i, das, (m, mapup n (second (const mk)) mas))

vsolveMeta :: (Monad m) => Name -> VTerm -> ContextT m ()
vsolveMeta n = updateMeta n . Solution

qsolveMeta :: (Monad m) => Name -> QTerm -> ContextT m ()
qsolveMeta n t = eval t >>= vsolveMeta n

-- `lookup n` doesn't check whether `n` is in scope.
-- It must be, but we'd better get an error if it's not.
getLookup :: (Monad m) => ContextT m (Env Int VTerm -> Head -> Maybe VTerm)
getLookup = do
  (_, das, (_, mas)) <- get 
  return $ \vs h -> case h of
    (Flex Def  n) -> fst <$> lookup n das
    (Flex Meta n) -> lookup n mas >>= tryGetSolution . snd
    (Var i)       -> lookup i vs

eval :: (Monad m) => QTerm -> ContextT m VTerm
eval t = flip pureEval t <$> getLookup

qnorm :: (Monad m) => QTerm -> ContextT m QTerm
qnorm = quote <.> eval

vnorm :: (Monad m) => VTerm -> ContextT m VTerm
vnorm = eval . quote
