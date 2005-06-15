{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  All rights reserved.

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from Haskell to Isabelle-HOLCF.
-}

module Comorphisms.Hs2HOLCF where

import Data.List
import Data.Maybe
import qualified Common.Lib.Map as Map
import Common.Result as Result
import Common.AS_Annotation

-- Haskell
import Haskell.HatParser as HatParser hiding (HsType)
import Haskell.HatAna as HatAna

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts as IsaConsts
import Isabelle.Translate as Translate

-- Programatica
import HsTypeStruct  
import HsKindStruct
import HsTypeMaps 
import HsName 
import HsIdent 
import TypedIds
import OrigTiMonad 

import TiTypes
import TiKinds
import TiInstanceDB -- as TiInst
 
import TiTEnv
import TiKEnv
import TiEnvFM

import PNT 
import PosName
import UniqueNames

import PropSyntaxRec 
import HsExpStruct
import HsPatStruct
import HsExpMaps
import HsPatMaps

import SyntaxRec
import TiPropDecorate
import PropSyntaxStruct
import HsDeclStruct
import HsGuardsStruct
import TiDecorate

------------------------------- Type synonims --------------------------------------

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
type HPat = SyntaxRec.HsPatI

type IsaSort = IsaSign.Sort
type IsaType = IsaSign.Typ
type IsaTerm = IsaSign.Term
type IsaPattern = IsaSign.Term
type IsaExKind = IsaSign.ExKind
type IsaTypeInsts = (TName, [(IsaClass, [(IsaType, [IsaClass])])])

type VaMap = Map.Map HsId HsScheme 
type TyMap = Map.Map HsId (Kind, HsTypeInfo)

------------------------------ Top level function ------------------------------
transTheory :: 
  HatAna.Sign -> [Named PrDecl] -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transTheory sign sens = do 
  sign' <- transSignature sign
  (sign'',sens'') <- transSentences sign' (map sentence sens)
  return (sign'', sens'')

------------------------------ Theory translation -------------------------------
{- Relevant theories in Programatica: base/Ti/TiClasses (for
tcTopDecls); property/parse2/Parse/PropPosSyntax (def of HsDecl).  -}

transSentences :: 
    IsaSign.Sign -> [PrDecl] -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transSentences sign ls = do xs <- mapM (transSentence sign) ls
                            ys <- return $ fixMRec xs
                            ac <- return $ newConstTab ys
                            nc <- return $ Map.union (constTab sign) ac
                            nsig <- return $ sign {constTab = nc}
                            return (nsig,ys) 

newConstTab :: [Named IsaSign.Sentence] -> ConstTab
newConstTab ls = Map.fromList [(extAxName x, extAxType x) | x <- ls]

transSentence :: 
    IsaSign.Sign -> PrDecl -> Result [Named IsaSign.Sentence]
transSentence sign (TiPropDecorate.Dec d) = case d of
             PropSyntaxStruct.Base p -> case p of
                HsDeclStruct.HsFunBind _ [x] -> do 
                    s <- transMatch sign x
                    return [s]
                _ -> return []
             _ -> return []

transMatch :: IsaSign.Sign -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds 
           -> Result (Named Sentence) 
transMatch sign t = case (t, constTab sign) of 
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _,
   cs) -> 
         let tx = transExp cs x
             df = showIsaName nm
             y = maybe (error "Haskell2IsabelleHOLCF, transMatch") id $ Map.lookup df cs
         in return $ NamedSen df True $ ConstDef $
              IsaEq (Const df y) $ termMAbs IsCont (map (transPat cs) ps) tx
  _ -> fail "Haskell2IsabelleHOLCF.transMatch, case not supported"

------------------- adding fixpoints ---------------------------------------------------------

fixMRec :: [[Named Sentence]] -> [Named Sentence]
fixMRec ls = addFixPoints $ getDepSent ls

addFixPoints :: [[Named Sentence]] -> [Named Sentence]
addFixPoints xs = concat $ map fixPoint xs

fixPoint :: [Named Sentence] -> [Named Sentence]
fixPoint xs = case xs of
  [a] -> case a of 
    NamedSen n w (ConstDef (IsaEq lh rh)) -> if sentDepOn a a           
       then [NamedSen n w $ ConstDef $ IsaEq lh $ fixPointRep lh rh]
       else xs
  a:as -> 
     let jn = joinNames (map extAxName xs)
         ks = [(extAxName x, extAxType x) | x <- xs]
         jv = Tuplex [(Free (extAxName x) (extAxType x)) | x <- xs] IsCont
         jt = typTuple (map extAxType xs)
         ys = [varsForMFuns ks (extRightH x) | x <- xs]
         jr = Tuplex ys IsCont -- Tuplex (map extRightH xs) IsCont - Tuplex ys IsCont
         jl = Const jn jt
         js = Fix $ IsaSign.Abs jv jt jr IsCont 
         mainfd = NamedSen jn True (ConstDef (IsaEq jl js)) 
         nks = [(extAxName x, (extAxType x, n)) | (x, n) <- listEnum xs]
         sF = elaborate (length xs) jn jt nks 
         origds = [NamedSen (extAxName x) True $ ConstDef (IsaEq (extLeftH x) (sF (extRightH x))) | x <- xs] 
     in mainfd : origds   
  [] -> []

fixPointRep :: Term -> Term -> Term
fixPointRep t1 t2 = case t1 of
  Const n x -> Fix $ IsaSign.Abs (Free n x) x (varForFun (n,x) t2) IsCont 
  _ -> error "Haskell2IsabelleHOLCF, fixPointRep"

{- replaces constants with variables of same name and type -}
varForFun ::  (VName,Typ) -> Term -> Term
varForFun (vn,ty) t = varsForFuns (sElem vn ty) (vn,ty) t 

sElem :: VName -> Typ -> VName -> Typ -> Maybe Term
sElem vn ty n t = if vn == n && typEq ty t then Just (Free n ty) else Nothing

{- replacement function -}
varsForMFuns :: [(VName,Typ)] -> Term -> Term
varsForMFuns ls t = varsForFuns (\c d -> tElem c d ls) ls t

tElem :: VName -> Typ -> [(VName,Typ)] -> Maybe Term
tElem x ty ls = let r = [t | (y,t) <- remove_duplicates ls, x == y, typEq ty t]
 in case r of 
  [] -> Nothing
  [a] -> Just (Free x ty)
  _ -> error "Haskell2IsabelleHOLCF, tElem"

elaborate :: Int -> VName -> Typ -> [(VName, (Typ, Int))] -> Term -> Term
elaborate mx vn ty ls t = varsForFuns (\c d -> ntElem mx c d vn ty ls) ls t

ntElem :: Int -> VName -> Typ -> VName -> Typ -> [(VName,(Typ,Int))] -> Maybe Term
ntElem mx x tx vn ty ls = let r = [(t,n) | (y,(t,n)) <- remove_duplicates ls, x == y, typEq tx t]
 in case r of 
  [] -> Nothing
  [(a,n)] -> Just $ tupleSelector mx n (Const vn ty) IsCont
  _ -> error "Haskell2IsabelleHOLCF, tElem"

tupleSelector :: Int -> Int -> Term -> Continuity -> Term
tupleSelector mx n t c
  | mx < 2 = error "Haskell2IsabelleHOLCF, tupleSelector - error 1"  
  | n == 0 = error "Haskell2IsabelleHOLCF, tupleSelector - error 2"
  | mx < n = error "Haskell2IsabelleHOLCF, tupleSelector - error 3"
  | n == mx = tupleSelect (n - 1) t c
  | True = termMAppl c (Const "cfst" noType) $ [tupleSelect (n - 1) t c]

tupleSelect :: Int -> Term -> Continuity -> Term
tupleSelect n t c = case n of
  0 -> t
  _ -> tupleSelect (n - 1) (termMAppl c (Const "csnd" noType) [t]) c

{- in term t, replaces variables, build according to f and ls, 
   for constants matching the VName and Typ parameters of f     -} 
varsForFuns :: 
  (VName -> Typ -> Maybe Term) -> a -> Term -> Term
varsForFuns f ls t = case t of
 IsaSign.Const n t1 -> maybe t id $ f n t1
 IsaSign.Abs v y x c -> IsaSign.Abs v y (varsForFuns f ls x) c
 IsaSign.App x y c -> IsaSign.App (varsForFuns f ls x) (varsForFuns f ls y) c
 IsaSign.If x y z c -> 
     IsaSign.If (varsForFuns f ls x) (varsForFuns f ls y) (varsForFuns f ls z) c 
 IsaSign.Case x ys -> 
     IsaSign.Case (varsForFuns f ls x) [(a,varsForFuns f ls b) | (a,b) <- ys]
 IsaSign.Let xs y -> 
     IsaSign.Let [(a,varsForFuns f ls b) | (a,b) <- xs] (varsForFuns f ls y)
 IsaSign.IsaEq x y -> IsaSign.IsaEq (varsForFuns f ls x) (varsForFuns f ls y) 
 IsaSign.Tuplex xs c -> IsaSign.Tuplex (map (varsForFuns f ls) xs) c
 IsaSign.Fix x -> IsaSign.Fix (varsForFuns f ls x)
 IsaSign.Paren x -> IsaSign.Paren (varsForFuns f ls x) 
 _ -> t  

extAxName :: Named Sentence -> VName
extAxName s = case s of 
  NamedSen n True _ -> n
  _ -> error "Haskell2IsabelleHOLCF, extAxName"

joinNames :: [VName] -> String
joinNames ls = concat [x ++ "_X" | x <- ls]

extAxType :: Named Sentence -> Typ
extAxType s = case s of 
  NamedSen _ True (ConstDef (IsaEq (Const _ t) _)) -> t
  _ -> error "Haskell2IsabelleHOLCF, extAxType"

typTuple :: [Typ] -> Typ
typTuple ts = case ts of 
  [] -> noType
  [a] -> a
  a:as -> mkContProduct a (typTuple as)

extLeftH :: Named Sentence -> Term
extLeftH s = case s of 
  NamedSen _ _ (ConstDef (IsaEq t _)) -> t
  _ -> error "Haskell2IsabelleHOLCF, extLeftH"

extRightH :: Named Sentence -> Term
extRightH s = case s of 
  NamedSen _ _ (ConstDef (IsaEq _ t)) -> t
  _ -> error "Haskell2IsabelleHOLCF, extRightH"

listEnum :: [a] -> [(a,Int)]
listEnum l = case l of
 [] -> []
 a:as -> (a,length (a:as)):(listEnum as)

----------------------------- equivalence between types modulo variables name -------------------

constEq :: Term -> Term -> Bool
constEq t1 t2 = case (t1,t2) of
  (Const m x, Const n y) -> if n == m && typEq x y then True else False
  _ -> False

litEq :: Term -> Term -> Bool
litEq t1 t2 = case (t1,t2) of
  (Free m x, Const n y) -> if n == m && typEq x y then True else False
  _ -> False

typEq :: Typ -> Typ -> Bool     --make some distinction for case noType??
typEq t1 t2 = case (t1,t2) of
 (IsaSign.Type _ _ ls1,IsaSign.Type _ _ ls2) -> 
    if typeId t1 == typeId t2 && typeSort t1 == typeSort t2 then typLEq ls1 ls2 else False
 (TFree _ _,TFree _ _) -> if typeSort t1 == typeSort t2 then True else False
 (TVar _ _,TVar _ _) -> if typeSort t1 == typeSort t2 then True else False
 _ -> False

typLEq :: [Typ] -> [Typ] -> Bool
typLEq ls1 ls2 = case (ls1,ls2) of
     ([],[]) -> True
     (a:as,b:bs) -> typEq a b && typLEq as bs
     _ -> False
 
------------------------------ Signature translation -----------------------------

transSignature :: HatAna.Sign -> Result IsaSign.Sign

transSignature sign = Result [] $ Just $ IsaSign.emptySign
  { baseSig = HsHOLCF_thy,
    tsig = emptyTypeSig 
           { 
             classrel = getClassrel (HatAna.types sign),
             abbrs = getAbbrs (HatAna.types sign),
             arities = getArities (HatAna.instances sign) 
           },
    constTab = getConstTab (HatAna.values sign),
    domainTab = getDomainTab (HatAna.values sign)
  }

------------------------------- Signature --------------------------------------
-------------------------------- Name translation -----------------------------
-- Translating to strings compatible with Isabelle

class IsaName a where
 showIsaName :: a -> IName
 showIsaString :: a -> String

showIsaS :: String -> IsaSign.IName
showIsaS = transStringT HOLCF_thy

instance IsaName String where
 showIsaName x = showIsaS x
 showIsaString x = x

showIsaHsN :: Show a => (String -> a) -> HsName.HsName -> a
showIsaHsN f t = case t of  
       Qual _ y -> f y
       UnQual w -> f w

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

instance IsaName a => IsaName (TiTypes.Type a) where
 showIsaString (Typ t) = case t of
  HsTyFun _ _  -> "Fun"
  HsTyApp _ _ -> "App"
  HsTyVar x -> showIsaString x
  HsTyCon x -> showIsaString x
  HsTyForall _ _ x -> showIsaString x

------------------------------- Kind translation ------------------------------

kindTrans :: Kind -> IsaKind
kindTrans x = case x of 
                 K HsKindStruct.Kstar -> IsaSign.Star
                 K (HsKindStruct.Kfun a b) -> IsaSign.Kfun (kindTrans a) (kindTrans b)
                 _ -> error "error, Hs2HOLCF.kindTrans,"

kindExTrans :: Kind -> IsaExKind
kindExTrans x = case x of 
                 K HsKindStruct.Kstar -> IKind IsaSign.Star
                 K (HsKindStruct.Kfun a b) -> IKind (IsaSign.Kfun (kindTrans a) (kindTrans b))
                 K HsKindStruct.Kpred -> IClass
                 K HsKindStruct.Kprop -> PLogic
                 _ -> error "Hs2HOLCF.kindExTrans, kind variables not supported"

------------------------------ Type translation -------------------------------
{- This signature translation takes after the one to Stratego, and relies on 
 Isabelle.Translation to solve naming conflicts. -}

transT :: Show d => (PNT -> IsaType) -> (PNT -> IsaType) -> (d -> IsaType) -> 
                    HsTypeStruct.TI PNT d -> IsaType
transT trIdV trIdC trT t =
  case HsTypeMaps.mapTI2 trIdV trIdC trT t of
    HsTyFun t1 t2 -> IsaSign.mkContFun t1 t2
    HsTyApp t1 t2 -> IsaSign.typeAppl t1 [t2]
    HsTyVar a -> a
    HsTyCon k -> k 
    _ -> not_supported "Type" t

-- error :: forall a. [Char] -> a
not_supported :: (Show t, Show i) => String -> HsTypeStruct.TI i t -> a
not_supported s x = error $ s++" Haskell2IsabelleHOLCF.transT, type not supported: "++show x

getLitName :: HsType -> PNT
getLitName (Typ t) = case t of 
   HsTyVar x -> x
   HsTyCon x -> x
   _ -> error "Type is not a literal (Haskell2IsabelleHOLCF.getLitName)"         

transIdV :: [HsType] -> PNT -> IsaType
transIdV c t = TFree (showIsaName t) (getSort c t)

getSort :: [HsType] -> PNT -> IsaSort
getSort c t = case c of 
   [] -> IsaSign.dom
   x:cs -> let a = getInstType x 
               b = getInstClass x
               d = getLitName a
               s = getSort cs t
               k = transClass b
               u = showIsaName d
               v = showIsaName t
           in if u == v && k /= IsaClass "Eq" && k /= IsaClass "Ord" then k:s else s                  

transTN :: String -> String -> String
transTN s1 s2 = case (s1,s2) of 
   ("Prelude","Bool") -> "tr"
   ("Prelude","Int") -> "int lift"
   _ -> transPath s1 s2 

transPath :: String -> String -> String
transPath s1 s2 = (showIsaName s1)++"_"++(showIsaName s2) 

transIdC :: PNT -> IsaType
transIdC t = let tfs = transFields t
  in 
  case (UniqueNames.orig t) of 
    UniqueNames.G (PlainModule m) n _ -> 
         IsaSign.Type (transTN m n) IsaSign.dom tfs 
    UniqueNames.G (MainModule m) n _ -> 
         IsaSign.Type (transPath m n) IsaSign.dom tfs 
    _ -> IsaSign.Type (showIsaName t) IsaSign.dom tfs

transFields ::  PNT -> [IsaType]
transFields t = case t of 
    PNT _ (TypedIds.Type q) _ -> 
          [TFree (showIsaS x) IsaSign.dom | (PN x _) <- TypedIds.fields q]
    PNT _ (TypedIds.FieldOf _ q) _ -> 
          [TFree (showIsaS x) IsaSign.dom | (PN x _) <- TypedIds.fields q]
    _ -> []
--    _ -> error "Haskell2IsabelleHOLCF.transFields"

transType :: [HsType] -> HsType -> IsaType
transType c (Typ t) = transT (transIdV c) transIdC (transType c) t

------------------------------ Class translation ------------------------------

mkIsaClass :: CName -> IsaClass
mkIsaClass n = IsaClass n

transClass :: HsType -> IsaClass
transClass x = case x of 
    Typ (HsTyCon c) -> IsaClass (showIsaName c)
    Typ _ -> error "Hs2HOLCF.transClass"
-- maybe need check for parameters?

----------------------------- auxiliary lift function ------------------------

liftMapByList :: (x -> [(a,b)]) -> ([(c,d)] -> y) -> (a -> c) -> (b -> d) -> x -> y
liftMapByList ma mb h k f = mb [(h a, k b) | (a, b) <- ma f] 

liftMapByListD :: (x -> [(a,b)]) -> ([(c,(d,e))] -> y) -> (a -> c) -> (b -> d) -> (a -> e) -> x -> y
liftMapByListD ma mb h k l f = mb [(h a, (k b, l a)) | (a, b) <- ma f] 

liftMapByListF :: 
   (x -> [(a,b)]) -> ([(c,d)] -> y) -> (a -> c) -> (b -> d) -> (a -> Bool) -> x -> y
liftMapByListF ma mb h k cs f = mb [(h a, k b) | (a, b) <- ma f, cs a] 

------------------------------- getting ConstTab ------------------------------

data IsaVT = IsaConst | IsaVal deriving (Eq, Show)
type AConstTab = Map.Map VName (Typ,IsaVT)

getConstTab ::  VaMap -> ConstTab
getConstTab f = Map.map fst (Map.filter (\x -> (snd x) == IsaVal) (getAConstTab f))  

getAConstTab ::  VaMap -> AConstTab
getAConstTab f =   
    liftMapByListD Map.toList Map.fromList showIsaName transFromScheme getValInfo f

getValInfo :: HsId -> IsaVT
getValInfo n = case n of 
   HsCon x -> IsaConst
   _ -> IsaVal

transFromScheme :: HsScheme -> IsaType
transFromScheme s = case s of 
    Forall _ _ (c TiTypes.:=> t) -> transType c t

----------------------------- getting Classrel (from KEnv) -----------------------

getClassrel ::  TyMap -> IsaSign.Classrel
getClassrel f = 
     liftMapByList Map.toList Map.fromList (mkIsaClass . showIsaName) transClassInfo f

transClassInfo :: (Kind, HsTypeInfo) -> [IsaClass]
transClassInfo p = map transClass (extClassInfo $ snd p)

extClassInfo :: HsTypeInfo -> [HsClass]
extClassInfo p = case p of 
        TiTypes.Class a _ _ _ -> map getInstType a 
        _ -> error "error Haskell2IsabelleHOLCF.extClassInfo"     
 
---------------------------- getting Abbrs (from KEnv) -----------------------------
 
getAbbrs ::  TyMap -> IsaSign.Abbrs
getAbbrs f = 
    liftMapByList Map.toList Map.fromList showIsaName transAbbrsInfo f

transAbbrsInfo :: (Kind, HsTypeInfo) -> ([TName], IsaType)
transAbbrsInfo p = let x = extAbbrsInfo (snd p) 
                   in (map showIsaName (fst x), transType [] (snd x))

extAbbrsInfo :: HsTypeInfo -> ([PNT], HsType)
extAbbrsInfo p = case p of 
           TiTypes.Synonym ls t -> (ls, t)
           _ -> error "extAbbrsInfo"
 
------------------------------ getting Arities ------------------------------------

getArities :: HsInstances -> IsaSign.Arities
getArities db = Map.fromList $ getIsaInsts db  

getIsaInsts :: HsInstances -> [IsaTypeInsts]
getIsaInsts db = map transTypeInsts (getTypeInsts db)

getTypeInsts :: HsInstances -> [(HsType, HsInstances)]
getTypeInsts db = 
  [(t, [x | x <- db, showIsaString (getMainInstType x) == showIsaString t]) 
                    | t <- remove_duplicates (map getMainInstType db)]

transTypeInsts :: (HsType, HsInstances) -> IsaTypeInsts
transTypeInsts (a,b) = (typeId $ transType [] a, map transInst b)
 
------------------------------ auxiliaries ----------------------------------------

removeEL :: Eq a => [[a]] -> [[a]]
removeEL ls = case ls of 
 a:as -> if a == [] then removeEL as else a:(removeEL as)
 [] -> []

remove_duplicates :: (Eq a) => [a] -> [a]
remove_duplicates ls = remove_dupes ls []

remove_dupes :: (Eq a) => [a] -> [a] -> [a]
remove_dupes ls ms = case ls of 
   x:rs -> if (elem x (rs ++ ms)) then remove_dupes rs ms else remove_dupes rs (x:ms)
   [] -> ms

getInstPrems :: HsInstance -> [HsPred]
getInstPrems (_, IE _ _ ps) = ps

getMainInstType :: HsInstance -> HsType
getMainInstType i = getInstType (fst i)

getMainInstClass :: HsInstance -> HsClass
getMainInstClass i = getInstClass (fst i)

getInstType :: HsPred -> HsType
getInstType x = case x of (Typ (HsTyApp _ t)) -> t
                          _ -> error "error, getInstType"
 
getInstClass :: HsPred -> HsType
getInstClass x = case x of (Typ (HsTyApp c _)) -> c
                           _ -> error "error, getInstClass"

-------------- corresponding change in IsaSign

transInst :: HsInstance -> (IsaClass, [(IsaType, [IsaClass])])
transInst i = let x = prepInst i in 
         (transClass $ fst x, [(transType [] a, map transClass b) | (a,b) <- snd x])

prepInst :: HsInstance -> (HsClass, [(HsType, [HsClass])])
prepInst i = (getMainInstClass i, prepInst1 i)

prepInst1 :: HsInstance -> [(HsType, [HsClass])]
prepInst1 i = 
  [(x, [getInstClass y | y <- getInstPrems i, showIsaString (getInstType y) == showIsaString x]) 
               | x <- remove_duplicates $ map getInstType (getInstPrems i)] 

--------------------------- checking mutual dependencies ---------------------------

abGetDep :: Eq a => (a -> a -> Bool) -> [[a]] -> [[a]]
abGetDep f ls = case ls of 
 x:xs -> 
   remove_duplicates $ removeEL (map remove_duplicates (checkDep (abCheckDep (mutRel f)) (xs) [x] []))
 [] -> []

{- used to check whether, given two lists of elements, there is one depending on the other -} 
abCheckDep :: (a -> a -> Bool) -> [a] -> [a] -> Bool
abCheckDep f as bs = genOr (\x -> genOr (f x) bs) as  

checkDep ::  ([x] -> [x] -> Bool) -> [[x]] -> [[x]] -> [[x]] -> [[x]]
checkDep f ls ms cs = case ls of 
  a:as -> case ms of 
     b:bs -> if (f a b) then checkDep f ((a ++ b):as) bs cs else checkDep f (a:as) bs (b:cs)
     [] -> checkDep f as (a:cs) []
  [] -> ms 

{- mutual dependence -} 
mutRel :: (a -> a -> Bool) -> a -> a -> Bool
mutRel f x y = f x y && f y x

depOn :: (a -> b -> Bool) -> (c -> a) -> (c -> [b]) -> c -> c -> Bool
depOn f g h x y = genOr (f (g x)) (h y) 

genOr :: (a -> Bool) -> [a] -> Bool
genOr f ys = case ys of 
               [] -> False
               x:xs -> if (f x) then True 
                           else (genOr f xs)

-- singList :: [a] -> [[a]]
-- singList list = [[a] | a <- list]
----------------------------- mutually recursive domains --------------------------

getDepDoms :: [[IsaSign.DomainEntry]] -> IsaSign.DomainTab
getDepDoms ls = abGetDep deDepOn ls   

deDepOn :: DomainEntry -> DomainEntry -> Bool
deDepOn x y = depOn subTypForm fst (concat . (map snd) . snd) x y

subTypForm :: Typ -> Typ -> Bool
subTypForm t1 t2 = case t2 of 
      IsaSign.Type a b cs -> 
                  if a == IsaSign.typeId t1 &&
                     b == IsaSign.typeSort t1 then True 
                  else genOr (subTypForm t1) cs
      _ -> False   

------------------------------- getting DomainTab -----------------------------

getDomainTab :: VaMap -> IsaSign.DomainTab 
getDomainTab f =  
   getDepDoms $ remove_duplicates [getDomainEntry (getAConstTab f) x | x <- Map.keys f, checkTyCons x]

checkTyCons :: HsId -> Bool
checkTyCons d = case d of 
  HsCon x -> True 
  _ -> False

getHsType :: VaMap -> HsId -> HsScheme
getHsType f n = case Map.lookup n f of 
    Just t -> t
    _ -> error "Haskell2IsabelleHOLCF.getHsType"

getDomainEntry :: AConstTab -> HsId -> [IsaSign.DomainEntry]
getDomainEntry ctab t = case t of
  HsCon (PNT _ (TypedIds.ConstrOf _ d) _) -> 
     [(getDomType ctab (showIsaName t), [(b, getFieldTypes ctab b) | 
            b <- [showIsaName c | (PN c _) <- map conName (constructors d)]])]
  _ -> []

getDomType :: AConstTab -> VName -> IsaType
getDomType ctab c = let x = Map.lookup c ctab in
                           case x of
                                  Nothing -> error "Haskell2IsabelleHOLCF.getDomType"
                                  Just y -> getHeadType $ fst y

getHeadType :: IsaType -> IsaType
getHeadType t = case t of 
  IsaSign.Type "dFun" _ [t1,t2] -> getHeadType t2
  _ -> t

getFieldTypes :: AConstTab -> VName -> [IsaType]
getFieldTypes ctab c = let x = Map.lookup c ctab in
                           case x of
                                  Nothing -> []
                                  Just y -> argTypes (fst y)

argTypes :: IsaType -> [IsaType]
argTypes a = case a of
    IsaSign.Type "dFun" _ [b,c] -> b:argTypes c
    _ -> [] 

{- ------------------------------ getting Type Constructors ---------------------
getTyCons :: TyMap -> VaMap -> Map.Map TName IsaType
getTyCons g f =  
     liftMapByListF Map.toList Map.fromList showIsaH transFromScheme (checkTyCons g) f 
-} --------------------------------- Expressions -------------------------------

mapEI5 :: (i1 -> i2) -> 
          (e1 -> e2) ->
          (p1 -> p2) ->
          EI i1 e1 p1 d t c -> EI i2 e2 p2 d t c
mapEI5 a b c e = HsExpMaps.mapEI a b c id id id e

-- transE :: IsaName i => (i -> VName) -> (e -> IsaTerm) -> (p -> IsaPattern) -> 
--            (HsExpStruct.EI i e p j h k) -> IsaTerm
transE :: (PNT -> VName) -> (e -> IsaTerm) -> (p -> IsaPattern) -> 
            (HsExpStruct.EI PNT e p j h k) -> IsaTerm
transE trId trE trP e =
 case (mapEI5 trId trE trP e) of 
   HsId (HsVar x)              -> Const "DIC" noType     
   HsApp x y                   -> termMAppl IsCont x [y]  
   HsLambda ps x               -> termMAbs IsCont ps x 
   HsIf x y z                  -> If x y z IsCont 
   HsTuple xs                  -> Tuplex xs IsCont 
   HsParen x                   -> Paren x
   _ -> Const "dummy" noType
--   _ -> error "Haskell2IsabelleHOLCF.transE, not supported"
--   HsId (HsCon c)              -> Const c noType
--   HsId (HsVar "==")              -> Const "Eq" noType     
--   HsLet ds e                  -> Let (map transPatBind ds) (transExp e) 
--   HsCase e ds                 -> Case e ds 

multiAbs :: [IsaPattern] -> IsaTerm -> IsaTerm
multiAbs ps t = case ps of 
  [] -> t
  a:as -> IsaSign.Abs a (termType a) (multiAbs as t) IsCont

transPatBind :: ConstTab -> PrDecl -> (IsaTerm,IsaTerm)
transPatBind cs s = case s of
  TiPropDecorate.Dec (PropSyntaxStruct.Base 
        (HsDeclStruct.HsPatBind _ p (HsGuardsStruct.HsBody e) _)) ->
                (transPat cs p, transExp cs e) 
 
transP :: IsaName i => (i -> VName) -> (p -> IsaPattern) -> 
            (HsPatStruct.PI i p) -> IsaPattern
transP trId trP p =
 case HsPatMaps.mapPI trId trP p of
   HsPId (HsVar x) -> Const "DIC" noType
   HsPTuple _ xs -> Tuplex xs IsCont 
   HsPParen x -> Paren x
   HsPWildCard -> Wildcard
   _ -> error "Haskell2IsabelleHOLCF.transP, not supported"
--   HsPList ps -> plist ps
--   HsPId (HsCon c) -> Const c noType
--   HsPLit _ lit -> litPat (transL lit) -- new
--   HsPApp c ps -> App x y IsCont
--   HsPAsPat x p -> AsPattern (x,p)
--   HsPIrrPat p -> twiddlePat p

class IsaName i => TransFunction i j k where
 transFun :: (j i) -> k

extVars :: IsaPattern -> VName
extVars p = case p of 
    Free x _ -> x 
    _ -> error "Haskell2IsabelleHOLCF.extVars"

transCN :: HsScheme -> PNT -> IsaTerm
transCN s x = let 
  y = showIsaName x
  z = transFromScheme s 
  f w = Const w z
  in
  if elem pcpo (typeSort z) then case pp x of
      "True" -> f "TT"
      "False" -> f "FF"
      _ -> f y
  else f y

transHV :: HsScheme -> PNT -> IsaTerm
transHV s x = let 
      n = showIsaName x 
      k = transFromScheme s
      tag = elem pcpo (typeSort k)
      in 
   case pp x of  
   "==" -> if tag == False then Const eq k
           else 
     (termMAbs IsCont [Free "x" noType, Free "y" noType] 
        (App (Const "Def" noType) (termMAppl NotCont (Const eq k) 
           [Free "x" noType, Free "y" noType]) NotCont))
   "&&" -> if tag == False then Const "op &" k
           else (Const "trand" k) 
   "||" -> if tag == False then Const "op |" k
           else (Const "tror" k) 
   "+" -> if tag == False then Const "op +" k
          else (termMAppl NotCont (Const "fliftbin" noType) [(Const "op +" k)]) 
   "-" -> if tag == False then Const "op -" k
          else (termMAppl NotCont (Const "fliftbin" noType) [(Const "op -" k)]) 
   "*" -> if tag == False then Const "op *" k
          else (termMAppl NotCont (Const "fliftbin" noType) [(Const "op *" k)]) 
   _ -> case x of
        PNT (PN _ (UniqueNames.G _ _ _)) _ _ -> Const n k 
        PNT (PN _ (UniqueNames.S _)) _ _ -> Free n k
        PNT (PN _ (UniqueNames.Sn _ _)) _ _ -> Free n k
        _ -> error "Haskell2IsabelleHOLCF, transHV"

transExp :: ConstTab -> PrExp -> IsaTerm
transExp cs t = case t of 
    (TiPropDecorate.Exp e) -> case e of
       HsLit _ (HsInt n) -> 
           Const ("(Def (" ++ (show n) ++ "::int))") (IsaSign.Type "int lift" [] [])
       HsLet (TiPropDecorate.Decs ds _) k -> 
          Let (map (transPatBind cs) ds) (transExp cs k) -- (transE showIsaName (transExp cs) (transPat cs) e) 
       _ -> transE showIsaName (transExp cs) (transPat cs) e
    TiPropDecorate.TiSpec w s _ -> case w of 
       HsVar x -> transHV s x
       HsCon x -> transCN s x
    TiPropDecorate.TiTyped x _ -> transExp cs x

transPat :: ConstTab -> PrPat -> IsaPattern
transPat cs t = case t of 
    (TiDecorate.Pat p) -> transP showIsaName (transPat cs) p
    (TiDecorate.TiPSpec w s _) -> case w of 
         HsVar x -> transHV s x
         HsCon x -> transCN s x
    (TiDecorate.TiPTyped x _) -> transPat cs x
    _ -> Bottom

termMAbs :: Continuity -> [Term] -> Term -> Term
termMAbs c ts t = 
 case ts of 
   [] -> t
   v:vs -> if v == (Const "DIC" noType) then (termMAbs c vs t) else 
      termMAbs c vs (IsaSign.Abs v (termType v) t c)  

termMAppl :: Continuity -> Term -> [Term] -> Term
termMAppl c t ts = 
 case (t,ts) of   
   (Const "inst__Prelude_Num_Int" _, [a]) -> a
   (Const "fromInteger" _, [a]) -> a
   (Const "derived__Prelude_Eq_Bool" _, [a]) -> a
   (_,[]) -> t
   (_,v:vs) -> if v == (Const "DIC" noType) then (termMAppl c t vs) else 
      case v of  
        (Const "inst__Prelude_Num_Int" _) -> (termMAppl c t vs)
        (Const "fromInteger" _) -> (termMAppl c t vs)
        (Const "derived__Prelude_Eq_Bool" _) -> (termMAppl c t vs)
        _ -> termMAppl c (App t v c) vs 

------------------ checking for mutually recursive functions --------------------------------------------

getDepSent :: [[Named Sentence]] -> [[Named Sentence]]
getDepSent ls = abGetDep sentDepOn ls   

sentDepOn :: Named Sentence -> Named Sentence -> Bool
sentDepOn x y = 
  depOn (\x y -> simTerms x y && typEq (termType x) (termType y)) (fst . sentAna) (snd . sentAna) x y 

sentAna :: Named Sentence -> (Term, [Term])
sentAna s = case s of
  NamedSen _ True (ConstDef (IsaEq l r)) -> (l, constFilter r)

simTerms :: Term -> Term -> Bool
simTerms t1 t2 = case (t1, t2) of
 (IsaSign.Const x _,  IsaSign.Const y _) -> if x == y then True else False
 (IsaSign.Free _ _, IsaSign.Free _ _) -> True
 (IsaSign.Var _ _, IsaSign.Var _ _) -> True
 (IsaSign.Bound _, IsaSign.Bound _) -> True
 (IsaSign.Abs _ _ _ c, IsaSign.Abs _ _ _ d) -> if c == d then True else False
 (If _ _ _ c, If _ _ _ d) -> if c == d then True else False
 (Case _ _, Case _ _) -> True
 (Let _ _, Let _ _) -> True
 (IsaEq _ _, IsaEq _ _) -> True
 (Fix _, Fix _) -> True
 (Bottom, Bottom) -> True
 (Paren x, y) -> simTerms x y
 (x, Paren y) -> simTerms x y
 (Wildcard, Wildcard) -> True
 _ -> False

constFilter :: Term -> [Term]
constFilter t = case t of
 IsaSign.Const _ _ -> [t]
 IsaSign.Abs _ _ x _ -> constFilter x
 IsaSign.App x y _ -> concat $ map constFilter [x,y]
 IsaSign.If x y z c -> concat $ map constFilter [x,y,z] 
 IsaSign.Case x ys -> concat $ map constFilter (x:(map snd ys))
 IsaSign.Let xs y -> concat $ map constFilter (y:(map snd xs))
 IsaSign.IsaEq x y -> concat $ map constFilter [x,y]
 IsaSign.Tuplex xs _ -> concat $ map constFilter xs
 IsaSign.Fix x -> constFilter x
 IsaSign.Paren x -> constFilter x
 _ -> [t]
 
