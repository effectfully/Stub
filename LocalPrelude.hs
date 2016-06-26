module LocalPrelude
  ( module LocalPrelude
  , module Debug.Trace
  , module Data.Maybe
  , module Data.Either
  , module Data.List
  , module Data.Functor.Identity
  , module Control.Applicative
  , module Control.Arrow 
  , module Control.Monad
  , module Control.Monad.Trans
  , module Control.Monad.Trans.Maybe
  , module Control.Monad.Trans.Reader
  , module Control.Monad.Trans.State
  , module Control.Monad.Trans.Except
  ) where

import Debug.Trace
import Data.Maybe
import Data.Either
import Data.List
import Data.Functor.Identity
import Control.Applicative
import Control.Arrow 
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.Maybe  (MaybeT(..))
import Control.Monad.Trans.Reader (ReaderT(..), withReaderT, ask, local)
import Control.Monad.Trans.State  (StateT(..), evalStateT, get, put, modify)
import Control.Monad.Trans.Except (ExceptT(..), runExceptT, throwE)

infixr 6 <.>
infixl 4 <<$>>, <<*>>, <&>
infixl 3 .>, <.
infixl 1 >>>=
infixl 2 ?>

(.*) = (.) . (.)

return2 :: (Monad n, Monad m) => a -> n (m a)
return2 = return . return

lift2 :: (MonadTrans t2, MonadTrans t1, Monad m, Monad (t1 m)) => m a -> t2 (t1 m) a
lift2 = lift . lift

(<.>) :: (Functor f) => (b -> c) -> (a -> f b) -> a -> f c 
g <.> f = fmap g . f

(<<$>>) :: (Functor g, Functor f) => (a -> b) -> g (f a) -> g (f b)
(<<$>>) = fmap . fmap

(<<*>>) :: (Applicative g, Applicative f) => g (f (a -> b)) -> g (f a) -> g (f b)
(<<*>>) = liftA2 (<*>)

(<&>) :: (Monad m) => m (a -> m b) -> m a -> m b
f <&> a = f >>= (a >>=)

(>>>=) :: (MonadTrans t, Monad m, Monad (t m)) => t m a -> (a -> m b) -> t m b
a >>>= f = a >>= lift . f

(=<<<) :: (MonadTrans t, Monad m, Monad (t m)) => (a -> m b) -> t m a -> t m b
(=<<<) = flip (>>>=)

(?>) :: MonadPlus m => Bool -> m a -> m a
True  ?> a = a
False ?> a = mzero

fst3 :: (a, b, c) -> a
fst3 (x1, x2, x3) = x1

snd3 :: (a, b, c) -> b
snd3 (x1, x2, x3) = x2

thd3 :: (a, b, c) -> c
thd3 (x1, x2, x3) = x3

fst4 :: (a, b, c, d) -> a
fst4 (x1, x2, x3, x4) = x1

snd4 :: (a, b, c, d) -> b
snd4 (x1, x2, x3, x4) = x2

first3 :: (a -> d) -> (a, b, c) -> (d, b, c)
first3 f (x1, x2, x3) = (f x1, x2, x3)

third3 :: (c -> d) -> (a, b, c) -> (a, b, d)
third3 f (x1, x2, x3) = (x1, x2, f x3)

first4 :: (a -> e) -> (a, b, c, d) -> (e, b, c, d)
first4 f (x1, x2, x3, x4) = (f x1, x2, x3, x4)

(.>) :: Functor f => a -> f b -> f (a, b)
x .> b = (,) x <$> b

(<.) :: Functor f => f a -> b -> f (a, b)
a <. y = flip (,) y <$> a

firstM :: Functor f => (a -> f c) -> (a, b) -> f (c, b)
firstM f (x, y) = f x <. y

secondM :: Functor f => (b -> f c) -> (a, b) -> f (a, c)
secondM g (x, y) = x .> g y



both :: (a -> Bool) -> a -> a -> Bool
both p x y = p x == p y

fromRight :: Either a b -> b
fromRight (Left  x) = error "fromRight"
fromRight (Right y) = y

tryInitLast :: [a] -> Maybe ([a], a)
tryInitLast  []    = Nothing
tryInitLast  [x]   = Just ([], x)
tryInitLast (x:xs) = first (x:) <$> tryInitLast xs

mapup :: Eq a => a -> (b -> b) -> [(a, b)] -> [(a, b)]
mapup x g  []            = []
mapup x g ((y, z) : yzs)
  | x == y    = (y, g z) : yzs
  | otherwise = (y, z)   : mapup x g yzs

zipFilter :: [Bool] -> [a] -> [a]
zipFilter  []           xs      = []
zipFilter (True  : bs) (x : xs) = x : zipFilter bs xs
zipFilter (False : bs) (x : xs) = zipFilter bs xs

zipWithEq :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithEq f  []     []    = Just []
zipWithEq f (x:xs) (y:ys) = (f x y :) <$> zipWithEq f xs ys
zipWithEq f  _      _     = Nothing

qnub :: Ord a => [a] -> [a]
qnub = map head . group . sort

isSingleton :: [a] -> Bool
isSingleton [_] = True
isSingleton  _  = False

isUniqueIn :: Eq a => a -> [a] -> Bool
isUniqueIn x = isSingleton . filter (x ==)

isUnique :: Ord a => [a] -> Bool
isUnique = all (null . tail) . group . sort

isSublistOf :: Eq a => [a] -> [a] -> Bool
xs `isSublistOf` ys = all (`elem` ys) xs

isUniqueSublistOf :: Eq a => [a] -> [a] -> Bool
isUniqueSublistOf xs ys = all (`isUniqueIn` ys) xs

fromMaybeT :: (Monad m) => m a -> MaybeT m a -> m a
fromMaybeT a m = runMaybeT m >>= maybe a return

withReaderTM :: (Monad m) => (s -> m r) -> ReaderT r m a -> ReaderT s m a
withReaderTM f a = ReaderT $ f >=> runReaderT a

readerToState :: (Functor m) => (s -> r) -> ReaderT r m a -> StateT s m a
readerToState f r = StateT $ \e -> (runReaderT r (f e)) <. e

modifyM :: (Monad m) => (s -> m s) -> StateT s m ()
modifyM f = StateT $ (,) () <.> f
