{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   The embedding comorphism from Haskell to Isabelle-HOLCF.
-}

module Comorphisms.Haskell2IsabelleHOLCF where

import Data.List
import Data.Maybe
import Logic.Logic as Logic
import Logic.Comorphism
import Common.Result as Result
import Common.Id as Id
import qualified Common.Lib.Map as Map
import Common.AS_Annotation

-- Haskell
import Haskell.Logic_Haskell as LH
import Haskell.HatParser as HatParser hiding (HsType)
import Haskell.HatAna as HatAna

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaConsts as IsaConsts
import Isabelle.Translate as Translate

-- Programatica
import FiniteMap
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
-- type HDecl i = PropPosSyntax.HsDecl i
-- type HExp i = PropPosSyntax.HsExp i
type HPat = SyntaxRec.HsPatI

type IsaSort = IsaSign.Sort
type IsaType = IsaSign.Typ
type IsaTerm = IsaSign.Term
type IsaPattern = IsaSign.Term
type IsaExKind = IsaSign.ExKind
type IsaTypeInsts = (TName, [(IsaClass, [(IsaType, [IsaClass])])])

type VaMap = Map.Map HsId HsScheme 
type TyMap = Map.Map HsId (Kind, HsTypeInfo)

------------------------------ Comorphism -----------------------------------------
-- The identity of the comorphism
data Haskell2IsabelleHOLCF = Haskell2IsabelleHOLCF deriving (Show)

instance Language Haskell2IsabelleHOLCF -- default definition is okay

instance Comorphism Haskell2IsabelleHOLCF -- multi-parameter class Com.
               Haskell ()
               HatParser.HsDecls PrDecl () ()
               HatAna.Sign HaskellMorphism
               () () ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               IsabelleMorphism () () ()  where
    sourceLogic Haskell2IsabelleHOLCF = Haskell
    sourceSublogic Haskell2IsabelleHOLCF = ()
    targetLogic Haskell2IsabelleHOLCF = Isabelle
    targetSublogic Haskell2IsabelleHOLCF = ()
    map_sentence Haskell2IsabelleHOLCF _ _ = 
        fail "map_sentence Haskell2IsabelleHOLCF not supoorted"
    map_morphism Haskell2IsabelleHOLCF mor = do
       (sig1,_) <- map_sign Haskell2IsabelleHOLCF (Logic.dom Haskell mor)
       (sig2,_) <- map_sign Haskell2IsabelleHOLCF (cod Haskell mor)
       inclusion Isabelle sig1 sig2
    map_theory Haskell2IsabelleHOLCF (sign, sens) = do
        sign' <- transSignature sign
        sens'' <- mapM (transSentence sign . sentence) sens
        return (sign', concat sens'')

------------------------------ Theory translation -------------------------------

transSentence :: HatAna.Sign -> PrDecl -> Result [Named IsaSign.Sentence]
transSentence sign (TiPropDecorate.Dec d) = case d of
             PropSyntaxStruct.Base p -> case p of
                HsDeclStruct.HsFunBind _ [x] -> do 
                    (nam, def) <- transMatch x
                    return [NamedSen nam $ ConstDef def]
                _ -> return []
             _ -> return []

-- fuctionDecl :: PNT -> [HsTypeI PNT] -> HsTypeI PNT -> IsaTerm
-- functionDecl n c t = 

{-
transMatchList ::  [HsDeclStruct.HsMatchI PNT PrExp PrPat ds] -> Result IsaTerm
transMatchList ls = do ts <- transMatchListR ls
                       return $ Fix (mkIsaOrM ts) 

mkIsaOrM :: [IsaTerm] -> IsaTerm
mkIsaOrM ts = case ts of
  [] -> IsaSign.Bottom
  x:xs -> IsaConsts.mkIsaOr x (mkIsaOrM xs)

transMatchListR ::  [HsDeclStruct.HsMatchI PNT PrExp PrPat ds] -> Result [IsaTerm]
transMatchListR ls = case ls of
   [] -> return [IsaSign.Bottom]
   x:xs -> do t <- transMatch x
              ts <- transMatchListR xs
              return (case xs of 
                       [] -> [t]
                       y:ys -> t:ts)
-}

{- Use the fact that hatAna2 (in HatAna) returns the HsDecls without modifying them (first component). Check how hatAna2 is used by
 the translation. It should not be hard to pick the unchecked values. Get them printed out by Hets with show_theory. Then see what 
can be done. Relevant theories in Programatica: base/Ti/TiClasses (for tcTopDecls); property/parse2/Parse/PropPosSyntax (def of HsDecl).
-}

-- fixWrap :: IsaTerm -> IsaTerm
-- fixWrap x = let y = (Free "XX" noType) in Fix (Abs y (App (App XEqXEqX y IsCont) x IsCont))

transMatch :: HsDeclStruct.HsMatchI PNT PrExp PrPat ds -> Result (IName, IsaTerm) 
transMatch t = case t of 
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _) -> 
         let tx = transExp x
             df = showIsaName nm
         in return $ (df, IsaEq (Const df noType) (termMAbs IsCont (map transPat ps) tx))
--         in return $ termMAppl IsCont (Const "IsaEq" noType) [termMAppl IsCont (Const (showIsaPNT nm) noType) (map transPat ps), Fix tx]
-- App (App (Const "IsaEq" noType) (Const (showIsaPNT nm) noType) IsCont) tx IsCont
--         in return $ App (App (Const "IsaEq" noType) (Const (showIsaPNT nm) noType) IsCont) tx IsCont
  _ -> warning ("",IsaSign.Bottom) "Haskell2IsabelleHOLCF.transMatch, case not supported" nullPos

------------------------------ Signature translation -----------------------------

transSignature :: HatAna.Sign -> Result IsaSign.Sign

transSignature sign = Result [] $ Just $ IsaSign.Sign 
  { baseSig = HOLCF_thy,
    tsig = emptyTypeSig 
           { 
             classrel = getClassrel (HatAna.types sign),
             abbrs = getAbbrs (HatAna.types sign),
             arities = getArities (HatAna.instances sign) 
           },
    constTab = getConstTab (HatAna.values sign),
    dataTypeTab = [],
    domainTab = getDomainTab (HatAna.values sign),
    showLemmas = False }

------------------------------- Signature --------------------------------------
-------------------------------- Name translation -----------------------------
-- Translating to strings compatible with Isabelle

class IsaName a where
 showIsaName :: a -> IName

showIsaS :: String -> IsaSign.IName
showIsaS x = transStringT HOLCF_thy x
-- showIsaS x = Translate.transString x

instance IsaName String where
 showIsaName x = showIsaS x

showIsaHsN :: HsName.HsName -> IName
showIsaHsN t = case t of  
       Qual (PlainModule x) y -> ((showIsaS x)++"_"++(showIsaS y))
       Qual (MainModule x) y -> ((showIsaS x)++"_"++(showIsaS y))
       UnQual w -> showIsaS w

instance IsaName HsName.HsName where
 showIsaName = showIsaHsN

instance IsaName PosName.HsName where
 showIsaName (SN x _) = showIsaName x

instance IsaName PNT.PName where
 showIsaName (PN x _) = showIsaName x

instance IsaName PNT where
 showIsaName (PNT x _ _) = showIsaName x

instance IsaName a => IsaName (HId a) where
 showIsaName t =  case t of
                 HsVar x -> showIsaName x
                 HsCon x -> showIsaName x

-------------------------------- Identifier translation -----------------------

idTrans :: IsaName a => HId a -> IsaSign.Term
idTrans t = case t of
                 HsVar x -> Free (showIsaName x) noType
                 HsCon x -> Const (showIsaName x) noType

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

getConstTab ::  VaMap -> IsaSign.ConstTab
getConstTab f = Map.map fst (Map.filter (\x -> (snd x) == IsaVal) (getAConstTab f))  

getAConstTab ::  VaMap -> IsaSign.AConstTab
getAConstTab f =   
    liftMapByListD Map.toList Map.fromList showIsaName transFromScheme getValInfo f

getValInfo :: HsId -> IsaSign.IsaVT
getValInfo n = case n of 
   HsCon x -> IsaConst
   _ -> IsaVal

transFromScheme :: HsScheme -> IsaType
transFromScheme s = case s of 
    Forall _ _ (c TiTypes.:=> t) -> transType c t
    _ -> error "Haskell2IsabelleHOLCF.transFromScheme"

----------------------------- getting Classrel (from KEnv) -----------------------

getClassrel ::  TyMap -> IsaSign.Classrel
getClassrel f = 
     liftMapByList Map.toList Map.fromList (mkIsaClass . showIsaName) transClassInfo f

transClassInfo :: (Kind, HsTypeInfo) -> [IsaClass]
transClassInfo p = map transClass (extClassInfo $ snd p)

extClassInfo :: HsTypeInfo -> [HsClass]
extClassInfo p = case p of 
        TiTypes.Class a _ _ _ -> map getInstType a -- ?? error ???
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
  [(t, [x | x <- db, getMainInstType x == t]) 
                    | t <- remove_duplicates (map getMainInstType db)]

transTypeInsts :: (HsType, HsInstances) -> IsaTypeInsts
transTypeInsts (a,b) = (typeId $ transType [] a, map transInst b)
 
------------------------------ auxiliaries ----------------------------------------

remove_duplicates :: (Eq a) => [a] -> [a]
remove_duplicates ls = remove_dupes ls []

remove_dupes :: (Eq a) => [a] -> [a] -> [a]
remove_dupes ls ms = case ls of 
   x:rs -> if (elem x (rs ++ ms)) then remove_dupes rs ms else remove_dupes rs (x:ms)
   [] -> ms

getInstPrems :: HsInstance -> [HsPred]
getInstPrems i = snd (snd i)

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
prepInst1 i = [(x, [getInstClass y | y <- getInstPrems i, getInstType y == x]) 
               | x <- map getInstType (getInstPrems i)] 


--------------------------- checking mutual dependencies -----------------------

getDepDoms :: [[IsaSign.DomainEntry]] -> IsaSign.DomainTab
getDepDoms ls = case ls of 
                  x:xs -> remove_duplicates (map remove_duplicates (checkDep (abCheckDep (mutDep subTypForm)) (xs) [x] []))
                  [] -> []

{- used to check whether, given two lists of domain entries, there is one that depends on the other -} 
abCheckDep :: (a -> a -> Bool) -> [a] -> [a] -> Bool
abCheckDep f as bs = genOr (\x -> genOr (f x) bs) as  

checkDep ::  ([x] -> [x] -> Bool) -> [[x]] -> [[x]] -> [[x]] -> [[x]]
checkDep f ls ms cs = case ls of 
                         a:as -> case ms of 
                                   b:bs -> if (f a b) then checkDep f ((a ++ b):as) bs cs else checkDep f (a:as) bs (b:cs)
                                   [] -> checkDep f as (a:cs) []
                         [] -> ms 

{-
checkDep ::  ([x] -> [x] -> Bool) -> [[x]] -> [[x]] -> [[x]] -> [[x]]
checkDep f ls ms cs = case ls of 
                         a:as -> case ms of 
                                   b:bs -> if (f a b) then checkDep f ((a ++ b):as) bs cs else checkDep f (a:as) bs (b:cs)
                                   [] -> checkDep f as cs []
                         [] -> ms 
-}

{- mutual dependance between domains -} 
mutDep :: (a -> b -> Bool) -> (a,[(c,[b])]) -> (a,[(c,[b])]) -> Bool
mutDep f x y = depOn f x y && depOn f y x

depOn :: (a -> b -> Bool) -> (a,[(c,[b])]) -> (a,[(c,[b])]) -> Bool
depOn f x y = case (x,y) of 
              ((m,_),(_,ns)) -> genOr (f m) (concat (map snd ns))                       

{-
depOn :: DomainEntry -> DomainEntry -> Bool
depOn x y = case (x,y) of 
              ((a,_),(_,bs)) -> genOr (subTypForm a) (concat (map snd bs))                       
-}

genOr :: (a -> Bool) -> [a] -> Bool
genOr f ys = case ys of 
               [] -> False
               x:xs -> if (f x) then True 
                           else (genOr f xs)

{-
wrapSubTypForm :: Typ -> DomainEntry -> Bool
wrapSubTypForm t d = 
-}

subTypForm :: Typ -> Typ -> Bool
subTypForm t1 t2 = case t2 of 
      IsaSign.Type a b cs -> 
                  if a == IsaSign.typeId t1 &&
                     b == IsaSign.typeSort t1 then True 
                  else genOr (subTypForm t1) cs
      _ -> False   

-- subSenForm :: 


-- singList :: [a] -> [[a]]
-- singList list = [[a] | a <- list]

------------------------------- getting DomainTab -----------------------------

getDomainTab :: VaMap -> IsaSign.DomainTab 
getDomainTab f =  
   getDepDoms $ remove_duplicates [getDomainEntry (getAConstTab f) x | x <- Map.keys f, checkTyCons x]
--   getDepDoms $ singList [getDomainEntry (getConstTab f) (getHsType f x) | x <- Map.keys f, checkTyCons g x]

-- getDomainTab :: TyMap -> VaMap -> IsaSign.DomainTab 
-- getDomainTab g f =  
--     getDepDoms $ singList [getDomainEntry (getConstTab f) (getHsType f x) | x <- Map.keys f]

checkTyCons :: HsId -> Bool
checkTyCons d = case d of 
  HsCon x -> True 
  _ -> False

getHsType :: VaMap -> HsId -> HsScheme
getHsType f n = case Map.lookup n f of 
    Just t -> t
    _ -> error "Haskell2IsabelleHOLCF.getHsType"

getDomainEntry :: IsaSign.AConstTab -> HsId -> [IsaSign.DomainEntry]
getDomainEntry ctab t = case t of
  HsCon (PNT _ (TypedIds.ConstrOf _ d) _) -> 
     [(getDomType ctab (showIsaName t), [(b, getFieldTypes ctab b) | 
            b <- [showIsaName c | (PN c _) <- map conName (constructors d)]])]
  _ -> []

getDomType :: IsaSign.AConstTab -> VName -> IsaType
getDomType ctab c = let x = Map.lookup c ctab in
                           case x of
                                  Nothing -> error "Haskell2IsabelleHOLCF.getTheType"
--                                  Nothing -> error "Haskell2IsabelleHOLCF.getFieldTypes"
                                  Just y -> getHeadType $ fst y

getHeadType :: IsaType -> IsaType
getHeadType t = case t of 
  IsaSign.Type "dFun" _ [t1,t2] -> getHeadType t2
  _ -> t

getFieldTypes :: IsaSign.AConstTab -> VName -> [IsaType]
getFieldTypes ctab c = let x = Map.lookup c ctab in
                           case x of
                                  Nothing -> []
--                                  Nothing -> error "Haskell2IsabelleHOLCF.getFieldTypes"
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

transE :: IsaName i => (i -> VName) -> (e -> IsaTerm) -> (p -> IsaPattern) -> 
            (HsExpStruct.EI i e p j h k) -> IsaTerm
transE trId trE trP e =
 case (mapEI5 trId trE trP e) of 
--   HsId (HsVar "==")              -> Const "Eq" noType     -- CHANGE!!!!
   HsId (HsVar x)              -> Const "DIC" noType     -- CHANGE!!!!
--   HsId (HsCon c)              -> Const c noType
   HsApp x y                   -> termMAppl IsCont x [y]  
--   HsLambda ps e               -> multiAbs ps e 
--   HsLet ds e                  -> Let ds e 
   HsIf x y z                  -> CIf x y z 
--   HsCase e ds                 -> Case e ds 
   HsTuple es                  -> Tuples es IsCont 
   HsParen e                   -> Paren e
   _ -> error "Haskell2IsabelleHOLCF.transE, not supported"

multiAbs :: [IsaPattern] -> IsaTerm -> IsaTerm
multiAbs ps t = case ps of 
  [] -> t
  a:as -> IsaSign.Abs a (termType a) (multiAbs as t) IsCont

transP :: IsaName i => (i -> VName) -> (p -> IsaPattern) -> 
            (HsPatStruct.PI i p) -> IsaPattern
transP trId trP p =
 case HsPatMaps.mapPI trId trP p of
   HsPId (HsVar x) -> Const "DIC" noType
--   HsPId (HsCon c) -> Const c noType
--   HsPLit _ lit -> litPat (transL lit) -- new
--   HsPApp c ps -> App x y IsCont
   HsPTuple ps -> Tuples ps IsCont 
--   HsPList ps -> plist ps
   HsPParen p -> Paren p
-- HsPRec
--   HsPAsPat x p -> AsPattern (x,p)
   HsPWildCard -> Wildcard
--   HsPIrrPat p -> twiddlePat p
--   _ -> not_supported "Pattern" p
   _ -> error "Haskell2IsabelleHOLCF.transP, not supported"

class IsaName i => TransFunction i j k where
 transFun :: (j i) -> k

-- instance TransFunction PNT HPat IsaPattern where
-- transFun = transPat

extVars :: IsaPattern -> VName
extVars p = case p of 
    Free x _ -> x 
    _ -> error "Haskell2IsabelleHOLCF.extVars"

transCN :: HsScheme -> PNT -> IsaTerm
transCN s x = let 
  y = showIsaName x
  z = transFromScheme s 
  f = \w -> Const w z
  in
  if elem pcpo (typeSort z) then case y of
      "TrueX" -> f "TT"
      "FalseX" -> f "FF"
      _ -> f y
  else f y

transExp :: PrExp -> IsaTerm
transExp t = case t of 
    (TiPropDecorate.Exp (HsLambda ps e)) -> termMAbs IsCont (map transPat ps) (transExp e)
    (TiPropDecorate.Exp e) -> transE showIsaName transExp transPat e
    (TiPropDecorate.TiSpec (HsVar x) s _) -> Free (showIsaName x) (transFromScheme s)
    (TiPropDecorate.TiSpec (HsCon x) s _) -> transCN s x
    (TiPropDecorate.TiTyped x _) -> transExp x
    _ -> Bottom
--    _ -> error "Haskell2IsabelleHOLCF.transExp"

-- transExp :: PropSyntaxRec.HsExpI PNT -> IsaTerm
-- transExp t = case t of 
--    (PropSyntaxRec.Exp e) -> transE showIsaS transExp transPat e

--    transE showIsaS transExp transE transLocalDecs e
--  where
--  transLocalDecs (a,b) = (transE a, transE b)

transPat :: PrPat -> IsaPattern
transPat x = case x of 
    (TiDecorate.Pat p) -> transP showIsaName transPat p
    (TiDecorate.TiPSpec (HsVar x) s _) -> Free (showIsaName x) (transFromScheme s)
    (TiDecorate.TiPSpec (HsCon x) s _) -> Const (showIsaName x) (transFromScheme s)
    (TiDecorate.TiPTyped x _) -> transPat x
    _ -> Bottom
--    _ -> error "Haskell2IsabelleHOLCF.transPat"
-- transPat :: SyntaxRec.HsPatI PNT -> IsaPattern
-- transPat (Pat p) = transP showIsaS transPat p

termMAbs :: Continuity -> [Term] -> Term -> Term
termMAbs c ts t = 
 case ts of 
   [] -> t
   v:vs -> if v == (Const "DIC" noType) then (termMAbs c vs t) else 
      termMAbs c vs (IsaSign.Abs v (termType v) t c)  

termMAppl :: Continuity -> Term -> [Term] -> Term
termMAppl c t ts = 
 case ts of 
   [] -> t
   v:vs -> if v == (Const "DIC" noType) then (termMAppl c t vs) else 
      termMAppl c (App t v c) vs 

