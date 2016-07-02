module Test where

import LocalPrelude
import Core
import Context
import TCM

infixr 5 ~>

forall :: String -> Syntax -> Syntax
forall n = Pi n (:?)

(~>) :: Syntax -> Syntax -> Syntax
(~>) = Pi "_"

var :: String -> Syntax
var n = App n []

it :: Syntax
it = forall "A" $ var "A" ~> var "A"

i :: Syntax
i = Lam "B" $ Lam "y" $ App "y" [] 

at :: Syntax
at =  forall "A"
   $  Pi "B" (var "A" ~> Star)
   $  (forall "x" $ App "B" [var "x"])
   ~> (forall "x" $ App "B" [var "x"])

a :: Syntax
a = Lam "A" $ Lam "B" $ Lam "f" $ Lam "x" $ App "f" [var "x"]

st :: Syntax
st = forall "A"
   $ Pi "B" (var "A" ~> Star)
   $ Pi "C" (forall "x" $ App "B" [var "x"] ~> Star)
   $ Pi "g" (forall "x" $ forall "y" $ App "C" [var "x", var "y"])
   $ Pi "f" (forall "x" $ App "B" [var "x"])
   $ forall "x"
   $ App "C" [var "x", App "f" [var "x"]]

s :: Syntax
s = Lam "A" $ Lam "B" $ Lam "C" $ Lam "g" $ Lam "f" $ Lam "x" $ App "g" [var "x", App "f" [var "x"]]

evalTCM1 :: TCM a -> Either String a
evalTCM1 = fst <.> runTCM

testit = evalTCM1 (stypecheck it Star)

-- Right (\B -> \y -> y,(A : Type) -> A -> A)
testi = evalTCM1 (stypecheck i it)

-- Right (\A -> \B -> \f -> \x -> f x,
--         (A : Type) -> (B : A -> Type) -> ((x : A) -> B x) -> (x : A) -> B x)
testa = evalTCM1 (stypecheck a at)

-- Right (\A -> \B -> \C -> \g -> \f -> \x -> g x (f x)
--         (A : Type) -> (B : A -> Type) -> (C : (x : A) -> (B x) -> Type) ->
---          (g : (x : A) -> (y : B x) -> C x y) -> (f : (x : A) -> B x) -> (x : A) -> C x (f x))
tests = evalTCM1 (stypecheck s st)

forCheckT1 :: Syntax
forCheckT1 = forall "A"
           $ forall "B"
           $ Pi "f" (forall "x" $ App "B" [var "x"])
           $ Pi "C" ((var "A" ~> Star) ~> Star)
           $ Pi "z" (App "C" [var "B"])
           $ App "C" [var "B"]

forCheck1 :: Syntax
forCheck1 = Lam "A" $ Lam "B" $ Lam "f" $ Lam "C" $ Lam "z" $ var "z"

-- Right (\A -> \B -> \f -> \C -> \z -> z,
--         (A : Type) -> (B : A -> Type) -> (f : (x : A) -> B x) ->
--           (C : (A -> Type) -> Type) -> (z : C B) -> C B)
testCheck1 = evalTCM1 (stypecheck forCheck1 forCheckT1)

getSyntax = evalTCM1 . lift . toCTerm

forCheckT2 :: Syntax
forCheckT2 = forall "A"
           $ Pi "f" (forall "B" $ forall "x" $ App "B" [var "x"])
           $ Pi "C" ((Pi "B" (var "A" ~> Star) $ forall "x" $ App "B" [var "x"]) ~> Star)
           $ Pi "z" (App "C" [var "f"])
           $ App "C" [var "f"]

forCheck2 :: Syntax
forCheck2 = Lam "A" $ Lam "f" $ Lam "C" $ Lam "z" $ var "z"

-- Right (\A -> \f -> \C -> \z -> z,
--         (A : Type) -> (f : (B : A -> Type) -> (x : A) -> B x) ->
--           (C : ((B : A -> Type) -> (x : A) -> B x) -> Type) -> (z : C f) -> C f)
testCheck2 = runTCM (stypecheck forCheck2 forCheckT2)

-- The expression

-- ∀ A -> (f : ∀ B x -> B x) -> (C : (B : A -> Type) -> ∀ x -> B x) -> C f -> C f

-- is elaborated to

-- (A : ?0) -> (f : (B : ?1 A) -> (x : ?2 A B) -> B x) ->
--   (C : (B : A -> Type) -> (x : ?3 A f B) -> B x) -> C f -> C f

-- `?0` is solved by `?0 ≡ Type`.

-- `B x` can't type check, because `B` doesn't have enough Πs in its type,
-- so it's replaced by `?4 A B x` which will compute to `B x` as soon as
-- there are enough Πs and `B x` is successfully type checked.

-- `?3` is solved by `?3 ≡ \A f B -> A`.

-- The expression now is

-- (A : Type) -> (f : (B : ?1 A) -> (x : ?2 A B) -> ?4 A B x) ->
--   (C : (B : A -> Type) -> (x : A) -> B x) -> C f -> C f

-- An attempt to type check `C f` forces unification of these two types:

-- (B : ?1 A)      -> (x : ?2 A B) -> ?4 A B x
-- (B : A -> Type) -> (x : A)      -> B x

-- `?1` is solved by `?1 ≡ \A -> A -> Type`.

-- Now there are enough Πs, so `?4 A B x` is type checked, which gives `?2 ≡ \A B -> A` and
-- `?4 ≡ \A B x -> B x`. It only remains to unify

-- (x : A) -> B x
-- (x : A) -> B x

-- which is trivial.

-- The final `C f` is type checked with all metas being already solved, so it's trivial too.

-- The fully elaborated expression:

-- (A : Type) -> (f : (B : A -> Type) -> (x : A) -> B x) ->
--   (C : (B : A -> Type) -> (x : A) -> B x) -> C f -> C f
