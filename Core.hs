module Core where

import LocalPrelude

type Env i a = [(i, a)]

--------------------

data Entry = Entry { getName :: !String, getId :: !Int }

type Frees = [Int]

data Head = Var  !Entry
          | Meta !Entry

unVar :: Head -> Maybe Entry
unVar (Var e) = Just e
unVar  _      = Nothing

headFreeVars :: Head -> Frees
headFreeVars (Var (Entry n i)) = [i]
headFreeVars  _                = []

headFreeVarsModulo :: Frees -> Head -> Frees
headFreeVarsModulo [] = headFreeVars
headFreeVarsModulo is = (\\ is) . headFreeVars

--------------------

type VType  = VTerm
type VSpine = [VTerm] -- Spines should be strict, right?
type VCon   = Env Int (String, VType) -- `IntMap`.

data VTerm = VStar
           | VPi   !Entry VType (VTerm -> VType)
           | VHead !Head
           | VLam  !Entry VType (VTerm -> VTerm)
           | VApp VTerm VTerm

fromHead :: (Entry -> a) -> (Entry -> a) -> Head -> a
fromHead f g (Var  e) = f e
fromHead f g (Meta e) = g e

vvar :: Entry -> VTerm
vvar = VHead . Var

vmeta :: Entry -> VTerm
vmeta = VHead . Meta

appVSpine :: VTerm -> VSpine -> VTerm
appVSpine (VLam _ _ k) (x:xs) = appVSpine (k x) xs
appVSpine  t            xs    = foldl' VApp t xs

etaExpand :: Entry -> VType -> VTerm -> VTerm
etaExpand e a = VLam e a . VApp

countVPis :: VType -> Int
countVPis (VPi e a b) = countVPis (b (vvar e)) + 1
countVPis  _          = 0

vcraft :: (Entry -> VType -> (VTerm -> VTerm) -> VTerm) -> VCon -> VType -> VType
vcraft binder inas = go inas (\vs -> unVar >=> flip lookup vs . getId) . quote where
  go :: VCon -> (Env Int VTerm -> Head -> Maybe VTerm) -> QType -> VType
  go  []                  k a = pureEval k a
  go ((i, (n, a)) : inas) k b = binder (Entry n i) a $ \x -> go inas (k . ((i, x):)) b

--------------------

type QType  = QTerm
type QSpine = [QTerm]
type QCon   = Env Int (String, QType)

data QTerm = QStar
           | QPi  !Entry QType QType
           | QLam !Entry QType QTerm
           | QApp !Head QSpine

qvar :: Entry -> QTerm
qvar e = QApp (Var e) []

qmeta :: Entry -> QTerm
qmeta e = QApp (Meta e) []

unQVar :: QTerm -> Maybe Entry
unQVar (QApp (Var e) []) = Just e
unQVar  _                = Nothing

isQVar :: QTerm -> Bool
isQVar = isJust . unQVar
  
isForeverNeutral :: QTerm -> Bool
isForeverNeutral (QApp (Var _) _) = True
isForeverNeutral  _               = False

vconToQCon :: VCon -> QCon
vconToQCon = map (second (second quote))

spineQApp :: QTerm -> QTerm -> QTerm
spineQApp (QApp h ts) t = QApp h (ts ++ [t])

allFreeVarsModulo :: Frees -> QTerm -> Frees
allFreeVarsModulo is  QStar                 = []
allFreeVarsModulo is (QPi  (Entry n i) a b) = allFreeVarsModulo is a ++ allFreeVarsModulo (i:is) b
allFreeVarsModulo is (QLam (Entry n i) a t) = allFreeVarsModulo (i:is) t
allFreeVarsModulo is (QApp h ts)            =
  headFreeVarsModulo is h ++ concatMap (allFreeVarsModulo is) ts

freeVarsModulo :: Frees -> QTerm -> Frees
freeVarsModulo is = qnub . allFreeVarsModulo is

freeVars :: QTerm -> Frees
freeVars = freeVarsModulo []

qcraft :: (Entry -> QType -> QTerm -> QTerm) -> QCon -> QTerm -> QTerm
qcraft binder  []                  t = t
qcraft binder ((i, (n, a)) : inas) t = binder (Entry n i) a (qcraft binder inas t)

pureEval :: (Env Int VTerm -> Head -> Maybe VTerm) -> QTerm -> VTerm
pureEval (!) = go [] where
  go :: Env Int VTerm -> QTerm -> VTerm
  go vs  QStar                   = VStar
  go vs (QPi  e@(Entry n i) a b) = VPi  e (go vs a) (\v -> go ((i, v) : vs) b)
  go vs (QLam e@(Entry n i) a t) = VLam e (go vs a) (\v -> go ((i, v) : vs) t)
  go vs (QApp h ts)              = fromMaybe (VHead h) (vs ! h) `appVSpine` map (go vs) ts

quote :: VTerm -> QTerm
quote  VStar       = QStar
quote (VPi  e a b) = QPi  e (quote a) (quote (b (vvar e)))
quote (VHead h)    = QApp h []
quote (VLam e a k) = QLam e (quote a) (quote (k (vvar e)))
quote (VApp f x)   = quote f `spineQApp` quote x

--------------------

type CType  = CTerm
type CSpine = [CTerm]
type CCon   = Env Int String

data CTerm = CStar
           | CPi  !Entry CType CType
           | CLam !Entry CTerm
           | CApp !Head CSpine
           | CMeta

type Equations  = [(VTerm, VTerm)]

data MetaKind = Guarded Equations QTerm
              | Check VType Int CTerm
              | Solution VTerm
              | Unknown
              deriving (Show)

cvar :: Entry -> CTerm
cvar e = CApp (Var e) []

craftCLams :: CCon -> CTerm -> CTerm
craftCLams  []            t = t
craftCLams ((i, n) : ins) t = CLam (Entry n i) (craftCLams ins t)

vconToCCon :: VCon -> CCon
vconToCCon = map (second fst)

isSolvable :: MetaKind -> Bool
isSolvable Unknown = True
isSolvable _       = False

tryGetSolution :: MetaKind -> Maybe VTerm
tryGetSolution (Solution t) = Just t
tryGetSolution  _           = Nothing

--------------------

data Syntax = Star
            | Pi String Syntax Syntax
            | Lam String Syntax
            | App String [Syntax]
            | (:?)

instance Eq Entry where
  Entry n i == Entry m j = i == j

instance Show Entry where
  show (Entry n i) = '?' : n ++ show i

instance Show Syntax where
  show  Star        = "Type"
  show (Pi "_" a b) = concat [parens (show a), " -> ", show b]
  show (Pi  n  a b) = concat ["(", n, " : ", show a, ")", " -> ", show b]
  show (Lam n  t)   = concat ["\\", n, " -> ", show t]
  show (App n [])   = n
  show (App n ts)   = concat . intersperse " " $ n : map (parens . show) ts
  show (:?)         = "_"

qtermToCTerm :: QTerm -> CTerm
qtermToCTerm  QStar       = CStar
qtermToCTerm (QPi  e a b) = CPi  e (qtermToCTerm a) (qtermToCTerm b)
qtermToCTerm (QLam e a t) = CLam e (qtermToCTerm t)
qtermToCTerm (QApp h ts)  = CApp h (map qtermToCTerm ts)

ctermToSyntax :: CTerm -> Syntax
ctermToSyntax = go [] where
  go :: Env Int String -> CTerm -> Syntax 
  go ns  CStar                 = Star
  go ns (CPi  (Entry n i) a b) = Pi  n (go ns a) (go ((i, n) : ns) b)
  go ns (CLam (Entry n i) t)   = Lam n (go ((i, n) : ns) t)
  go ns (CApp h ts)            =
    App (fromHead (\(Entry n i) -> fromMaybe ('\'':n) (lookup i ns)) show h) (map (go ns) ts)
  go ns  CMeta                 = (:?)

instance Show CTerm where
  show = show . ctermToSyntax

instance Show QTerm where
  show = show . qtermToCTerm

instance Show VTerm where
  show = show . quote
