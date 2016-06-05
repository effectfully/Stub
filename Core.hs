module Core where

import LocalPrelude

type Env i a = [(i, a)]

--------------------

type Name  = String
type Frees = [Int]

data Flex = Def
          | Meta
          deriving (Eq, Show)

data Head = Var  !Int
          | Flex !Flex !Name
          deriving (Eq, Show)

unVar :: Head -> Maybe Int
unVar (Var i) = Just i
unVar  _      = Nothing

headFreeVars :: Head -> Frees
headFreeVars (Var i)     = [i]
headFreeVars (Flex _ n ) = []

headFreeVarsModulo :: Frees -> Head -> Frees
headFreeVarsModulo [] = headFreeVars
headFreeVarsModulo is = (\\ is) . headFreeVars

--------------------

type VType  = VTerm
type VSpine = [VTerm] -- Spines should be strict, right?

data VTerm = VStar
           | VPi !Name VType (VTerm -> VType)
           | VHead !Head
           | VLam !Name VType (VTerm -> VTerm)
           | VApp VTerm VTerm

fromHead :: (Int -> a) -> (Flex -> Name -> a) -> Head -> a
fromHead g h (Var i)    = g i
fromHead g h (Flex f n) = h f n

vvar :: Int -> VTerm
vvar = VHead . Var

vflex :: Flex -> Name -> VTerm
vflex = VHead .* Flex

vdef :: Name -> VTerm
vdef = vflex Def

vmeta :: Name -> VTerm
vmeta = vflex Meta

-- Do something with names or generate them later if needed?
craftVLams :: [VTerm] -> (VSpine -> VTerm) -> VTerm
craftVLams  []    k = k []
craftVLams (a:as) k = VLam "" a $ \x -> craftVLams as (k . (x:))

appVSpine :: VTerm -> VSpine -> VTerm
appVSpine (VLam _ _ k) (x:xs) = appVSpine (k x) xs
appVSpine  t            xs    = foldl' VApp t xs

etaExpand :: Name -> VType -> VTerm -> VTerm
etaExpand n a = VLam n a . VApp

--------------------

type QType  = QTerm
type QSpine = [QTerm]

data QTerm = QStar
           | QPi  !Name !Int QType QType
           | QLam !Name !Int QType QTerm
           | QApp !Head QSpine
           deriving (Show)

qvar :: Int -> QTerm
qvar i = QApp (Var i) []

qmeta :: Name -> QTerm
qmeta n = QApp (Flex Meta n) []

unQVar :: QTerm -> Maybe Int
unQVar (QApp (Var i) []) = Just i
unQVar  _                = Nothing

isQVar :: QTerm -> Bool
isQVar = isJust . unQVar
  
isForeverNeutral :: QTerm -> Bool
isForeverNeutral (QApp (Var i) _) = True
isForeverNeutral  _               = False

allFreeVarsModulo :: Frees -> QTerm -> Frees
allFreeVarsModulo is  QStar         = []
allFreeVarsModulo is (QPi  n i a b) = allFreeVarsModulo is a ++ allFreeVarsModulo (i:is) b
allFreeVarsModulo is (QLam n i a t) = allFreeVarsModulo (i:is) t
allFreeVarsModulo is (QApp h ts)    = headFreeVarsModulo is h ++ concatMap (allFreeVarsModulo is) ts

freeVarsModulo :: Frees -> QTerm -> Frees
freeVarsModulo is = qnub . allFreeVarsModulo is

freeVars :: QTerm -> Frees
freeVars = freeVarsModulo []

craftQLamsFrom :: [(Int, QType)] -> QTerm -> QTerm
craftQLamsFrom  []            t = t
craftQLamsFrom ((i, a) : ias) t = QLam "" i a (craftQLamsFrom ias t)

spineQApp :: QTerm -> QTerm -> QTerm
spineQApp (QApp n ts) t = QApp n (ts ++ [t])

pureEval :: (Env Int VTerm -> Head -> Maybe VTerm) -> QTerm -> VTerm
pureEval (!) = go [] where
  go :: Env Int VTerm -> QTerm -> VTerm
  go vs  QStar         = VStar
  go vs (QPi  n i a b) = VPi  n (go vs a) (\v -> go ((i, v) : vs) b)
  go vs (QLam n i a t) = VLam n (go vs a) (\v -> go ((i, v) : vs) t)
  go vs (QApp h ts)    = fromMaybe (VHead h) (vs ! h) `appVSpine` map (go vs) ts

--------------------

type CType  = CTerm
type CSpine = [CTerm]

data CTerm = CStar
           | CPi  !Name !Int CType CType
           | CLam !Name !Int CTerm
           | CApp !Head CSpine
           | CMeta
           deriving (Show)

type Equations  = [(VTerm, VTerm)]

data MetaKind = Guarded Equations QTerm
              | Check CTerm
              | Solution VTerm
              | Unknown

cvar :: Int -> CTerm
cvar i = CApp (Var i) []

isSolvable :: MetaKind -> Bool
isSolvable Unknown = True
isSolvable _       = False

tryGetSolution :: MetaKind -> Maybe VTerm
tryGetSolution (Solution t) = Just t
tryGetSolution  _           = Nothing

--------------------

data Syntax = Star
            | Pi Name Syntax Syntax
            | Lam Name Syntax
            | App Name [Syntax]
            | (:?)

-- Closed terms only.
toSyntax :: QTerm -> Syntax
toSyntax = go [] where
  go :: Env Int Name -> QTerm -> Syntax 
  go ns  QStar         = Star
  go ns (QPi  n i a b) = Pi  n (go ns a) (go ((i, n) : ns) b)
  go ns (QLam n i a t) = Lam n (go ((i, n) : ns) t)
  go ns (QApp h ts)    = App (fromHead (fromJust . flip lookup ns) (const id) h) (map (go ns) ts)

{-toSyntax :: QTerm -> Syntax
toSyntax = go [] where
  go :: Env Int Name -> QTerm -> Syntax 
  go ns  QStar         = Star
  go ns (QPi  n i a b) = Pi  n (go ns a) (go ((i, n) : ns) b)
  go ns (QLam n i a t) = Lam n (go ((i, n) : ns) t)
  go ns (QApp h ts)    = App (fromHead (\i -> fromMaybe ("Var " ++ show i) $ lookup i ns) (const id) h) (map (go ns) ts)-}

parens :: String -> String
parens s
  | ' ' `elem` s = "(" ++ s ++ ")"
  | otherwise    = s

instance Show Syntax where
  show  Star        = "Type"
  show (Pi "_" a b) = concat [parens (show a), " -> ", show b]
  show (Pi  n  a b) = concat ["(", n, " : ", show a, ")", " -> ", show b]
  show (Lam n t)    = concat ["\\", n, " -> ", show t]
  show (App n [])   = n
  show (App n ts)   = concat $ intersperse " " [n, ts >>= parens . show]
