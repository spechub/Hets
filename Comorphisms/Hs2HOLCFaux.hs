{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  Asimilar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable (depends on programatica using MPTC)

auxiliary functions for the embedding comorphism from Haskell to Isabelle
-}

module Comorphisms.Hs2HOLCFaux
    ( PrDecl
    , removeEL
    , extAxType
    , fixMRec
    , newConstTab
    , getTermName
    , extRightH
    , IsaSort
    , IsaType
    , IsaPattern
    , IsaTerm
    , IsaName(..)
    , xDummy
    , termMAbs
    , termMAppl
    , PrExp
    , PrPat
    , renVars
    , remove_duplicates
    , HsType
    , HsScheme
    , HsId
    , getInstClass
    , getInstType
    , repVarClass
    , constrVarClass
    , getLitName
    , transTN
    , transPath
    , showIsaS
    , funFliftbin
    , VaMap
    , AConstTab
    , liftMapByListD
    , nothingFiOut
    , IsaTypeInsts
    , IsaVT(..)
    , TyMap
    , liftMapByList
    , HsTypeInfo
    , HsInstance
    , HsInstances
    , extClassInfo
    , extAbbrsInfo
    , groupInst
    , getMainInstType
    , prepInst
    , checkTyCons
    , getDepDoms
    , getDomType
    , getFieldTypes
    ) where

import Data.List
import Data.Maybe
import qualified Common.Lib.Map as Map
import Common.AS_Annotation

-- Haskell (Programatica)
import SourceNames
import TiTypes
import TiKinds
import TiInstanceDB -- as TiInst

import PNT
import PosName
import UniqueNames

import SyntaxRec
import TiPropDecorate
import PropSyntaxStruct as HsName

import TiDecorate

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts as IsaConsts
import Isabelle.Translate as Translate

------------------------------- TYPE synonyms ---------------------------------
------------------ Haskell ----------------------------------------------------

type HsInstance = TiInstanceDB.Instance PNT
type HsInstances = [TiInstanceDB.Instance PNT]
type HsPred = TiTypes.Pred PNT
type HsType = TiTypes.Type PNT
type HsClass = TiTypes.Type PNT
type HsScheme = TiTypes.Scheme PNT
type HsId = HsIdentI PNT
type HsTypeInfo = TiTypes.TypeInfo PNT
type PrDecl = TiPropDecorate.TiDecl PNT
type PrExp = TiPropDecorate.TiExp PNT
type PrPat = TiDecorate.TiPat PNT

type HId i = HsIdentI i

type VaMap = Map.Map HsId HsScheme
type TyMap = Map.Map HsId (Kind, HsTypeInfo)

------------------ Isabelle ---------------------------------------------------

type IsaSort = IsaSign.Sort
type IsaType = IsaSign.Typ
type IsaTerm = IsaSign.Term
type IsaPattern = IsaSign.Term
type IsaTypeInsts = (TName, [(IsaClass, [(IsaType, [IsaClass])])])

----------------------------- list functions ----------------------------------

removeEL :: [[a]] -> [[a]]
removeEL = filter (not . null)

remove_duplicates :: Eq a => [a] -> [a]
remove_duplicates = nub . reverse

listEnum :: [a] -> [(a, Int)]
listEnum l = zip l [1..]

---------------------------------- filters -----------------------------------

nothingFiOut :: [(a, (Maybe b, c))] -> [(a, (b, c))]
nothingFiOut ls = [(x, (y, w)) | (x, (Just y, w)) <- ls]

--------------------------------- lifting function ---------------------------

liftMapByList :: (x -> [(a, b)]) -> ([(c, d)] -> y)
              -> (a -> c) -> (b -> d) -> x -> y
liftMapByList ma mb h k f = mb [(h a, k b) | (a, b) <- ma f]

liftMapByListD :: (x -> [a]) -> ([c] -> y) -> (a -> b1)
               -> (a -> b2) -> ([(b1, b2)] -> [c]) -> x -> y
liftMapByListD l1 l2 h k g f = l2 $ g [ (h a, k a) | a <- l1 f]

--------------------------- generic checking of mutual dependencies ----------

abGetDep :: Eq a => (a -> a -> Bool) -> [[a]] -> [[a]]
abGetDep f ls = case ls of
 x:xs ->
   remove_duplicates $
      removeEL (map remove_duplicates (checkDep (abCheckDep (mutRel f))
                                                    (xs) [x] []))
 [] -> []

{- called to check whether, given two lists of elements, one depends
on the other. -}
abCheckDep :: (a -> a -> Bool) -> [a] -> [a] -> Bool
abCheckDep f as bs = any (\x -> any (f x) bs) as

checkDep :: ([x] -> [x] -> Bool) -> [[x]] -> [[x]] -> [[x]] -> [[x]]
checkDep f ls ms cs = case ls of
  a:as -> case ms of
     b:bs ->
        if (f a b) then checkDep f ((a ++ b):as) bs cs else
                   checkDep f (a:as) bs (b:cs)
     [] -> checkDep f as (a:cs) []
  [] -> ms

-- mutual dependence
mutRel :: (a -> a -> Bool) -> a -> a -> Bool
mutRel f x y = f x y && f y x

depOn :: (a -> b -> Bool) -> (c -> a) -> (c -> [b]) -> c -> c -> Bool
depOn f g h x y = any (f (g x)) (h y)

------------------------ HASKELL representation -------------------------------
--------------------------- check functions -----------------------------------

checkTyCons :: HsId -> Bool
checkTyCons d = case d of
  HsCon _ -> True
  _ -> False

------------------------------ get functions -------------------------------
------------------------ getting info from Haskell types ----------------------

getLitName :: HsType -> PNT
getLitName (Typ t) = case t of
   HsTyVar x -> x
   HsTyCon x -> x
   _ -> error "Type is not a literal (Haskell2IsabelleHOLCF.getLitName)"

------------------------ getting class and type ouf of predicate --------------

getInstType :: HsPred -> HsType
getInstType x = case x of (Typ (HsTyApp _ t)) -> t
                          _ -> error "error, getInstType"

getInstClass :: HsPred -> HsType
getInstClass x = case x of (Typ (HsTyApp c _)) -> c
                           _ -> error "error, getInstClass"

---------------------------- getting class information -----------------------

extClassInfo :: HsTypeInfo -> [HsClass]
extClassInfo p = case p of
        TiTypes.Class a _ _ _ -> map getInstType a
        _ -> error "error Haskell2IsabelleHOLCF.extClassInfo"

--------------------------- getting info on type syns ------------------------

extAbbrsInfo :: HsTypeInfo -> ([PNT], HsType)
extAbbrsInfo p = case p of
           TiTypes.Synonym ls t -> (ls, t)
           _ -> error "extAbbrsInfo"

----------- getting arity information from Haskell instances -----------------

getInstPrems :: HsInstance -> [HsPred]
getInstPrems (_, IE _ _ ps) = ps

getMainInstType :: HsInstance -> HsType
getMainInstType i = getInstType (fst i)

getMainInstClass :: HsInstance -> HsClass
getMainInstClass i = getInstClass (fst i)

prepInst :: HsInstance -> (HsClass, [(HsType, [HsClass])])
prepInst i = (getMainInstClass i, prepInst1 i)

prepInst1 :: HsInstance -> [(HsType, [HsClass])]
prepInst1 i =
  [(x, [getInstClass y | y <-
          getInstPrems i, showIsaHsTypeString (getInstType y)
                           == showIsaHsTypeString x])
               | x <- remove_duplicates $ map getInstType (getInstPrems i)]

-------------------------- ISABELLE representation ---------------------------
-------------------------------- constants -----------------------------------

xDummy :: IsaTerm
xDummy = conDouble "dummy"

holEq :: IsaTerm -> IsaTerm -> IsaTerm
holEq t1 t2 = termMAppl NotCont (con eqV) [t1, t2]

getTermName :: Term -> String
getTermName a = case a of
  Const x _ -> new x
  Free x _ -> new x
  _ -> "_"

-------------------------------- Name translation ----------------------------
-- Translating to strings compatible with Isabelle

class IsaName a where
 showIsaName :: a -> String
 showIsaString :: a -> String

showIsaS :: String -> String
showIsaS = transConstStringT HOLCF_thy

instance IsaName String where
  showIsaName x = showIsaS x
  showIsaString x = x

showIsaHsN :: Show a => (String -> a) -> HsName.HsName -> a
showIsaHsN f t = case t of
       Qual _ y -> f y
       UnQual w -> f w

instance IsaName PNT.PId where
  showIsaName (PN x _) = showIsaS x
  showIsaString (PN x _) = x

instance IsaName HsName.HsName where
  showIsaName = showIsaHsN showIsaS
  showIsaString = showIsaHsN id

instance IsaName PosName.HsName where
  showIsaName (SN x _) = showIsaName x
  showIsaString (SN x _) = showIsaString x

instance IsaName PNT.PName where
  showIsaName (PN x _) = showIsaName x
  showIsaString (PN x _) = showIsaString x

instance IsaName PNT where
  showIsaName (PNT x _ _) = showIsaName x
  showIsaString (PNT x _ _) = showIsaString x

instance IsaName a => IsaName (HId a) where
  showIsaName t =  case t of
                 HsVar x -> showIsaName x
                 HsCon x -> showIsaName x
  showIsaString t =  case t of
                 HsVar x -> showIsaString x
                 HsCon x -> showIsaString x

showIsaHsTypeString :: HsType -> String
showIsaHsTypeString (Typ t) = case t of
    HsTyFun _ _  -> "Fun"
    HsTyApp _ _ -> "App"
    HsTyVar x -> showIsaString x
    HsTyCon x -> showIsaString x
    HsTyForall _ _ x -> showIsaHsTypeString x

----------- auxiliary name functions (inessentially) depending on IsaSign ----

joinNames :: [String] -> String
joinNames = concatMap (++ "_X")

transTN :: Continuity -> String -> String -> String
transTN c s1 s2 = case (c,s1,s2) of
   (IsCont,"Prelude","Bool") -> "tr"
   (IsCont,"Prelude","Int") -> "dInt"
   (IsCont,"Prelude","Integer") -> "dInt"
   (IsCont,"Prelude","Rational") -> "dRat"
   (IsCont,"Prelude","[]") -> "llist"
   (IsCont,"Prelude","(,)") -> "*"
   (NotCont,"Prelude","Bool") -> "bool"
   (NotCont,"Prelude","Int") -> "int"
   (NotCont,"Prelude","Integer") -> "int"
   (NotCont,"Prelude","Rational") -> "Rat"
   (NotCont,"Prelude","[]") -> "list"
   (NotCont,"Prelude","(,)") -> "*"
   _ -> transPath s1 s2

transPath :: String -> String -> String
transPath s1 s2 = showIsaName s1 ++ "_" ++ showIsaName s2

-------------------------- TYPES ----------------------------------------------
------------------------ tuples, lifting --------------------------------------

typTuple :: Continuity -> [Typ] -> Typ
typTuple c ts = case ts of
  [] -> noType
  [a] -> a
  a : as -> (case c of
               IsCont -> mkContProduct
               NotCont -> prodType) a (typTuple c as)

----------------------------- equivalence of types modulo variables name ------

typEq :: Typ -> Typ -> Bool     --make some distinction for case noType??
typEq t1 t2 = t1 == noType || t2 == noType || case (t1, t2) of
  (IsaSign.Type _ _ ls1, IsaSign.Type _ _ ls2) ->
      typeId t1 == typeId t2 && typeSort t1 == typeSort t2 && typLEq ls1 ls2
  (TFree _ _, TFree _ _) -> typeSort t1 == typeSort t2
  (TVar _ _, TVar _ _) -> typeSort t1 == typeSort t2
  _ -> False

typLEq :: [Typ] -> [Typ] -> Bool
typLEq ls1 ls2 = case (ls1, ls2) of
     ([], []) -> True
     (a : as, b : bs) -> typEq a b && typLEq as bs
     _ -> False

------------------------------- replacement functions -------------------------

-- constrains variables in t with sort constraints in cs
constrVarClass :: IsaType -> [(IsaType,Sort)] -> IsaType
constrVarClass t cs = typeVarsRep addSort [(typeId x,y) | (x,y) <- cs] t

addSort :: [(TName,Sort)] -> TName -> Sort -> Maybe Typ
addSort cs n s = do
     as <- Map.lookup n (Map.fromList cs)
     return $ TFree n $ remove_duplicates $ s ++ as

-- replaces in t varibles of class c with nt
repVarClass :: IsaType -> IsaClass -> IsaType -> IsaType
repVarClass t c nt = typeVarsRep repVC (c,nt) t

repVC :: (IsaClass, IsaType) -> TName -> IsaSort -> Maybe IsaType
repVC (c, t) _ s = if elem c s then return t else Nothing

typeVarsRep :: (a -> TName -> Sort -> Maybe IsaType) -> a -> IsaType -> IsaType
typeVarsRep f ls t = case t of
    IsaSign.Type n s vs -> IsaSign.Type n s (map (typeVarsRep f ls) vs)
    IsaSign.TFree n s -> maybe t id $ f ls n s
    IsaSign.TVar _ _ -> t

------------------ more extraction and replacement functions ------------------

unifyTVars :: [IsaType] -> (IsaType,[IsaType])
unifyTVars ls = case chkTHead ls of
    False -> error "Hs2HOLCFaux,unifyTVars"
    True -> case ls of
        IsaSign.Type "=>" _ [i, _] : _ ->
           (i, [b | IsaSign.Type "=>" _ [_, b] <- ls])
        _ -> error "Hs2HOLCFaux,uTV"

chkTHead :: [IsaType] -> Bool
chkTHead ls = case ls of
   IsaSign.Type "=>" _ [x, _] : IsaSign.Type "=>" s [y, m] : ns ->
      if typEq x y then
         chkTHead (IsaSign.Type "=>" s [y, m] : ns) else False
   [IsaSign.Type "=>" _ _] -> True
   _ -> False

renTVars :: [Typ] -> [Typ]
renTVars ls = [renTVar b a | (a, b) <- listEnum ls]
 where
  renTVar n t =
    case t of
      TFree x s -> if take 2 x == "vX" then t else
                       TFree (x ++ "XX" ++ show n) s
      IsaSign.Type a b cs -> IsaSign.Type a b $ map (renTVar n) cs
      _ -> t

---------------------------- Instances ----------------------------------------

groupInst :: [IsaTypeInsts] -> [IsaTypeInsts]
groupInst db =
  remove_duplicates [(fst y,
        remove_duplicates $ concat
                      [snd x | x <- db, fst x == fst y]) | y <- db]

------------------------- DATATYPES -------------------------------------------
----------------------- getting mutually recursive domains in Isabelle --------

getDepDoms :: [[IsaSign.DomainEntry]] -> IsaSign.DomainTab
getDepDoms ls = abGetDep deDepOn ls

deDepOn :: DomainEntry -> DomainEntry -> Bool
deDepOn x y = depOn subTypForm fst (concat . (map snd) . snd) x y

subTypForm :: Typ -> Typ -> Bool
subTypForm t1 t2 = case t2 of
      IsaSign.Type a b cs ->
                  if a == IsaSign.typeId t1 &&
                     b == IsaSign.typeSort t1 then True
                  else any (subTypForm t1) cs
      _ -> False

------------------------ getting info about domaintab -------------------------

type AConstTab = Map.Map VName (Typ,IsaVT)
data IsaVT = IsaConst | IsaVal deriving (Eq, Show)

getDomType :: AConstTab -> VName -> IsaType
getDomType ctab c = let x = Map.lookup c ctab in
                           case x of
                           Nothing -> error "Haskell2IsabelleHOLCF.getDomType"
                           Just y -> getHeadType $ fst y

isFunArrow :: String -> Bool
isFunArrow name = elem name [funS, cFunS]

getHeadType :: IsaType -> IsaType
getHeadType t = case t of
  IsaSign.Type name _ [_, t2] | isFunArrow name -> getHeadType t2
  _ -> t

getFieldTypes :: AConstTab -> VName -> [IsaType]
getFieldTypes ctab c = let x = Map.lookup c ctab in
                           case x of
                                  Nothing -> []
                                  Just y -> argTypes (fst y)

argTypes :: IsaType -> [IsaType]
argTypes a = case a of
    IsaSign.Type name _ [b, c] | isFunArrow name -> b : argTypes c
    _ -> []

-------------------------- TERMS ----------------------------------------------
-------- lifting, tuples, multiple abstractions and applications, fixpoints ---

funFliftbin :: Term -> Term
funFliftbin f = termMAppl NotCont (conDouble fliftbinS) [f]

termMAbs :: Continuity -> [Term] -> Term -> Term
termMAbs c ts t =
 case ts of
   [] -> t
   v:vs -> if isDicConst v then (termMAbs c vs t) else
      IsaSign.Abs v (termType v) (termMAbs c vs t) c

termMAppl :: Continuity -> Term -> [Term] -> Term
termMAppl c t ts =
  let prelTest vn = any (\x -> isPrefixOf x $ IsaSign.orig vn)
               [ "inst__Prelude_"
               , "fromInteger"
               , "derived__Prelude_"]
 in case (t, ts) of
   (Const vn _, [a]) | isDicConst t || prelTest vn -> a
   (_, []) -> t
   (_, v : vs) -> case v of
         Const vn _ | isDicConst v || prelTest vn -> termMAppl c t vs
         _ -> termMAppl c (App t v c) vs

----------------------- connectives -------------------------------------------

tupleSelector :: Int -> Int -> Term -> Continuity -> Term
tupleSelector mx n t c
  | mx < 2 = error "Haskell2IsabelleHOLCF, tupleSelector - error 1"
  | n == 0 = error "Haskell2IsabelleHOLCF, tupleSelector - error 2"
  | mx < n = error "Haskell2IsabelleHOLCF, tupleSelector - error 3"
  | n == mx = tupleSelect (n - 1) t c
  | True = termMAppl c (conDouble (case c of
                                     IsCont -> "cfst"
                                     NotCont -> "fst"))
                              $ [tupleSelect (n - 1) t c]

tupleSelect :: Int -> Term -> Continuity -> Term
tupleSelect n t c = case n of
  0 -> t
  _ -> tupleSelect (n - 1)
     (termMAppl c (conDouble (case c of
                                IsCont -> "csnd"
                                NotCont -> "snd")) [t]) c

------------------------------------- term filters ----------------------------

isDicConst :: Term -> Bool
isDicConst t = case t of
    Const vn _ | IsaSign.orig vn == "DIC"  -> True
    _ -> False

constFilter :: Term -> [Term]
constFilter t = case t of
 IsaSign.Const _ _ -> [t]
 IsaSign.Abs _ _ x _ -> constFilter x
 IsaSign.App x y _ -> concat $ map constFilter [x,y]
 IsaSign.If x y z _ -> concat $ map constFilter [x,y,z]
 IsaSign.Case x ys -> concat $ map constFilter (x:(map snd ys))
 IsaSign.Let xs y -> concat $ map constFilter (y:(map snd xs))
 IsaSign.IsaEq x y -> concat $ map constFilter [x,y]
 IsaSign.Tuplex xs _ -> concat $ map constFilter xs
 IsaSign.Fix x -> constFilter x
 IsaSign.Paren x -> constFilter x
 _ -> [t]

elPos :: Int -> [Term] -> Term -> Maybe Int
elPos n ls x = case (listEnum ls) of
  [] -> Nothing
  a : as -> if constEq x (fst a) then Just $ (snd a + (n - length ls))
                                 else elPos n (map fst as) x

-------------------- subterm extraction -------------------------------------

extFBody :: Term -> (Term, [Term])
extFBody t' = let (x, ys) = extFB t' [] in (x, reverse ys)
 where
  extFB t as = case t of
     IsaSign.Abs x _ b _ -> extFB b (x : as)
     _ -> (t, as)

extTBody :: Term -> (Term, [Term])
extTBody t' = let (x,ys) = extTB t' [] in (x, reverse ys)
 where
  extTB t as = case t of
     IsaSign.App a x _ -> extTB a (x : as)
     _ -> (t, as)

------------------- eliminating case expressions ---------------------------

destCaseS :: Continuity -> IsaTerm -> IsaTerm -> [IsaTerm] -- t is def rh
destCaseS c d t =
    [holEq (termMAppl c d xs) y | (xs,y) <- destCaseU (extFBody t,[])]

destCaseU :: ((IsaTerm,[IsaPattern]),[IsaPattern]) -> [([IsaPattern],IsaTerm)]
destCaseU ((t,rs),ks) = case (t,rs) of
    (Case v ls, vv : vs) -> if v == vv
          then [(ks ++ [l], termMAbs NotCont vs m) | (l,m) <- ls]
          else destCaseU ((t,vs), ks ++ [vv])
    _ -> error "Hs2HOLCFaux, destCase"

destCase :: IsaTerm -> (VName -> VName) -> [(IsaPattern,IsaTerm)]
destCase t f = let w = extFBody t in case w of
    (Case v ls, _ : vs) -> case v of
          Free n tt ->
                [(renVars (Free (f n) tt) [l] l,
                         -- repl. l if l is a var.
                  renVars (Free (f n) tt)
                         [l] (termMAbs NotCont vs m)) | (l, m) <- ls]
          _ -> [(l,termMAbs NotCont vs m) | (l, m) <- ls]
    _ -> error "Hs2HOLCFaux, destCase"

----------------------------- equivalence on terms ---------------------------

constEq :: Term -> Term -> Bool
constEq t1 t2 = case (t1,t2) of
  (Const m x, Const n y) -> n == m && typEq x y
  _ -> False

{- this functions was actually meant to compare only constructors -
check out, there might be bugs -}

simTerms :: Term -> Term -> Bool
simTerms t1 t2 = case (t1, t2) of
 (IsaSign.Const x _,  IsaSign.Const y _) -> x == y
 (IsaSign.Free _ _, IsaSign.Free _ _) -> True
 (IsaSign.Var _ _, IsaSign.Var _ _) -> True
 (IsaSign.Bound _, IsaSign.Bound _) -> True
 (IsaSign.Abs _ _ _ c, IsaSign.Abs _ _ _ d) -> c == d
 (If _ _ _ c, If _ _ _ d) -> c == d
 (Case _ _, Case _ _) -> True
 (Let _ _, Let _ _) -> True
 (IsaEq _ _, IsaEq _ _) -> True
 (Fix _, Fix _) -> True
 (Bottom, Bottom) -> True
 (Tuplex _ _, Tuplex _ _) -> True
 (Paren x, y) -> simTerms x y
 (x, Paren y) -> simTerms x y
 (Wildcard, Wildcard) -> True
 _ -> False

------------------------ replacement functions -------------------------------

{- in term t, replaces variable f for variables in ls     -}
renVars ::  Term -> [Term] -> Term -> Term
renVars f ls t = case t of
 IsaSign.Free _ _ -> if elem t ls then f else t
 IsaSign.Abs v y x c -> IsaSign.Abs v y (renVars f ls x) c
 IsaSign.App x y c -> IsaSign.App (renVars f ls x) (renVars f ls y) c
 IsaSign.If x y z c ->
     IsaSign.If (renVars f ls x) (renVars f ls y) (renVars f ls z) c
 IsaSign.Case x ys ->
     IsaSign.Case (renVars f ls x) [(a,renVars f ls b) | (a,b) <- ys]
 IsaSign.Let xs y ->
     IsaSign.Let [(a,renVars f ls b) | (a,b) <- xs] (renVars f ls y)
 IsaSign.IsaEq x y -> IsaSign.IsaEq (renVars f ls x) (renVars f ls y)
 IsaSign.Tuplex xs c -> IsaSign.Tuplex (map (renVars f ls) xs) c
 IsaSign.Fix x -> IsaSign.Fix (renVars f ls x)
 IsaSign.Paren x -> IsaSign.Paren (renVars f ls x)
 _ -> t

renFuns :: (Term -> Maybe Term) -> Term -> Term
renFuns f t = case t of
 IsaSign.Abs v y x c -> IsaSign.Abs v y (renFuns f x) c
 IsaSign.App x y c -> maybe (IsaSign.App (renFuns f x) (renFuns f y) c) id
        $ f t
 IsaSign.If x y z c ->
     IsaSign.If (renFuns f x) (renFuns f y) (renFuns f z) c
 IsaSign.Case x ys ->
     IsaSign.Case (renFuns f x) [(a,renFuns f b) | (a,b) <- ys]
 IsaSign.Let xs y ->
     IsaSign.Let [(a,renFuns f b) | (a,b) <- xs] (renFuns f y)
 IsaSign.IsaEq x y -> IsaSign.IsaEq (renFuns f x) (renFuns f y)
 IsaSign.Tuplex xs c -> IsaSign.Tuplex (map (renFuns f) xs) c
 IsaSign.Fix x -> IsaSign.Fix (renFuns f x)
 IsaSign.Paren x -> IsaSign.Paren (renFuns f x)
 _ -> t

---------------------- SENTENCES ---------------------------------------------
--------------------- getting info from sentences ----------------------------

newConstTab :: Continuity -> [Named IsaSign.Sentence] -> ConstTab
newConstTab c ls = case c of
  IsCont -> Map.empty
  NotCont -> Map.fromList [(mkVName $ extAxName x, extAxType x) | x <- ls]

extAxName :: Named Sentence -> String
extAxName s = senName s

extAxType :: Named Sentence -> Typ
extAxType s = case s of
  NamedSen _ True _ (ConstDef (IsaEq (Const _ t) _)) -> t
  NamedSen _ True _
    (RecDef _ ((App (App _ (App (Const _ t) _ _) _) _ _ : _) : _)) -> t
  _ -> noType

extFunTerm :: Named Sentence -> Term
extFunTerm s = case s of
  NamedSen _ _ _ (ConstDef (IsaEq t _)) -> fst $ extTBody t
  _ -> error "Hs2HOLCFaux, extFunTerm"

extLeftH :: Named Sentence -> Term
extLeftH s = case s of
  NamedSen _ _ _ (ConstDef (IsaEq t _)) -> t
  _ -> error "Hs2HOLCFaux, extLeftH"

extRightH :: Named Sentence -> Term
extRightH s = case s of
  NamedSen _ _ _ (ConstDef (IsaEq _ t)) -> t
  _ -> error "Hs2HOLCFaux, extRightH"

{- left comp is the def name, right comp are the constants in the def  -}
sentAna :: Named Sentence -> (Term, [Term])
sentAna s = case s of
  NamedSen _ True _ (ConstDef (IsaEq l r)) -> (l, constFilter r)
  _ -> error "Hs2HOLCFaux, sentAna"

------------------ checking for mutually recursive function defs -------------

getDepSent :: [[Named Sentence]] -> [[Named Sentence]]
getDepSent ls = abGetDep sentDepOn ls

sentDepOn :: Named Sentence -> Named Sentence -> Bool
sentDepOn x y =
  depOn (\ u v -> simTerms u v && typEq (termType u) (termType v))
            (fst . sentAna) (snd . sentAna) x y

------------------- adding fixpoints ---------------------------------------

fixMRec :: Continuity -> [[Named Sentence]] -> [Named Sentence]
fixMRec c ls = addFixPoints c $ getDepSent ls

addFixPoints :: Continuity -> [[Named Sentence]] -> [Named Sentence]
addFixPoints c xs = concat $ map (fixPoint c) xs

fixPoint :: Continuity -> [Named Sentence] -> [Named Sentence]
fixPoint c xs = case xs of
  [a] -> if sentDepOn a a
         then case a of
           NamedSen l m n (ConstDef (IsaEq lh rh)) -> case c of
             IsCont ->
                [NamedSen l m n $ RecDef "fixrec" [[holEq lh rh]]]
             NotCont -> [NamedSen l m n $ RecDef "primrec"
                                               [destCaseS c lh rh]]
           _ -> error "Hs2HOLCFaux, fixPoint"
         else xs
  _ : _ -> case c of
    IsCont -> let
         jn = joinNames (map extAxName xs) -- name is ininfluential here
         ys = [[holEq (extLeftH x) $ extRightH x] | x <- xs]
      in [NamedSen jn True False $ RecDef "fixrec" ys]
    NotCont -> let
         jj = joinNames (map extAxName xs)
         jn = mkVName jj
         jt1 = unifyTVars (map extAxType xs)
         jt = mkFunType (fst jt1)
                (typTuple NotCont (renTVars $ snd jt1))
         jl = Const jn jt
         n = length xs
         rs = map extRightH xs
         ls = map extFunTerm xs
         yys = [destCase x (\ _ -> jn) | x <- rs]
         yyys = reassemble yys
         zs = [(p,Tuplex (map (renFuns (newFCons (Const jn noType) ls)) ts)
                                                                  NotCont)
                           | (p,ts) <- Map.toList yyys]
         os = [mkNewDef x jj n m | (x,m) <- listEnum xs]
         ps = (NamedSen jj True False $ makeRecDef jl zs):os
      in ps
  [] -> []

makeRecDef :: Term -> [(Term,Term)] -> Sentence
makeRecDef t ls =
 RecDef "primrec" [map (\x -> holEq (App t (fst x) NotCont) (snd x)) ls]

mkNewDef :: Named Sentence -> String -> Int -> Int -> Named Sentence
mkNewDef s z x y = let a = NotCont in case s of
   NamedSen l m n (ConstDef (IsaEq lh rh)) -> case (lh, extFBody rh) of
     (Const _ _, (_, w : ws)) ->
        NamedSen l m n (ConstDef (IsaEq lh $
           termMAbs a (w:ws) $ termMAppl a (tupleSelector x y
                 (App (conDouble z) w a) a) ws))
     _ -> error "Hs2HOLCFaux, mkNewDef 2"
   _ -> error "Hs2HOLCFaux, mkNewDef 1"

reassemble :: [[(Term,Term)]] -> Map.Map Term [Term] -- [(b, [c])]
reassemble ls = foldr
 (\ (ft, sd) ms ->
     Map.insert ft (sd : Map.findWithDefault [] ft ms) ms)
   Map.empty (concat ls)

newFCons :: Term -> [Term] -> Term -> Maybe Term
newFCons t ls k = case k of
 App n w NotCont -> case elPos (length ls) ls n of
   Nothing -> Nothing
   Just i ->
      Just $ tupleSelector (length ls) i (IsaSign.App t w NotCont) NotCont
 _ -> Nothing
