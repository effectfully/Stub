module Test where

import LocalPrelude
import Core
import Context
import TCM

infixr 5 ~>

var :: String -> Syntax
var n = App n []

(~>) :: Syntax -> Syntax -> Syntax
(~>) = Pi "_"

it :: Syntax
it = Pi "A" (:?) $ var "A" ~> var "A"

i :: Syntax
i = Lam "B" $ Lam "y" $ App "y" [] 

at :: Syntax
at =  Pi "A" (:?)
   $  Pi "B" (var "A" ~> Star)
   $  (Pi "x" (:?) $ App "B" [var "x"])
   ~> (Pi "x" (:?) $ App "B" [var "x"])

a :: Syntax
a = Lam "A" $ Lam "B" $ Lam "f" $ Lam "x" $ App "f" [var "x"]

evalTCM1 :: TCM a -> Either String a
evalTCM1 = fst <.> runTCM

testit = evalTCM1 (stypecheck it Star)

-- Right (\B -> \y -> y,(A : *) -> A -> A)
testi = evalTCM1 (stypecheck i it)

-- Right (\A -> \B -> \f -> \x -> f x,(A : *) -> (B : A -> *) -> ((x : A) -> B x) -> (x : A) -> B x)
testa = evalTCM1 (stypecheck a at)

getSyntax t = evalTCM1 (trackFreesToTCM $ toCTerm t)
