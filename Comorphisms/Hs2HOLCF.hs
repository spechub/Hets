{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from Haskell to Isabelle-HOLCF.
-}

module Comorphisms.Hs2HOLCF where

import Debug.Trace

import Data.List
import Data.Maybe
import qualified Common.Lib.Map as Map
import Common.Result as Result
import Common.AS_Annotation
import Comorphisms.Hs2HOLCFaux as Hs2HOLCFaux

-- Haskell
import Haskell.HatParser as HatParser hiding (HsType)
import Haskell.HatAna as HatAna

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

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts as IsaConsts
import Isabelle.Translate as Translate

------------------------------ Top level function ------------------------------
transTheory :: 
  HatAna.Sign -> [Named PrDecl] -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transTheory sign sens = do 
  sign' <- transSignature sign
  (sign'',sens'') <- -- trace (show $ arities $ tsig sign') $ 
          transSentences sign' (map sentence sens)
  return (sign'', sens'')

------------------------------ Theory translation -------------------------------
{- Relevant theories in Programatica: base/Ti/TiClasses (for 
tcTopDecls); property/parse2/Parse/PropPosSyntax (def of HsDecl).  -}

data ExpRole = FunDef | InstDef

transSentences :: 
    IsaSign.Sign -> [PrDecl] -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transSentences sign ls = do xx <- mapM (transSentence sign FunDef) ls
                            xs <- return [[s] | [s] <- xx, extAxType s /= noType]
                            ys <- -- trace ("\n" ++ (show xs)) $ 
                                  return $ fixMRec xs
                            ac <- return $ newConstTab ys
                            nc <- return $ Map.union (constTab sign) ac
                            nsig <- return $ sign {constTab = nc}
                            zz <- mapM (transSentence nsig InstDef) ls
                            zw <- return $ concat zz
                            zs <- return [s | s <- zw, extAxType s /= noType]
                            return (nsig, ys ++ zs) 

transSentence :: IsaSign.Sign -> ExpRole -> PrDecl -> Result [Named IsaSign.Sentence]
transSentence sign a (TiPropDecorate.Dec d) = case d of
  PropSyntaxStruct.Base p -> case (a,p) of
    (FunDef,  HsDeclStruct.HsFunBind _ [x]) -> do 
        k <- transMatch sign x
        return [k]             
    (InstDef, HsInstDecl _ _ _ t (TiPropDecorate.Decs ds _)) -> do
        q <- mapM (transIMatch sign t) 
             [y | TiPropDecorate.Dec (PropSyntaxStruct.Base (HsDeclStruct.HsFunBind _ [y])) <- ds]  
        return q 
    _ -> return []
  _ -> return []

makeSentence :: String -> ConstTab -> IsaType -> VName -> [PrPat] -> IsaTerm -> Named Sentence
makeSentence d cs y df ps tx = 
  if tx == xDummy then NamedSen d True $ ConstDef $ IsaEq xDummy $ xDummy 
  else NamedSen d True $ ConstDef $
       IsaEq (Const df y) $ termMAbs IsCont (map (transPat cs) ps) tx

--------------------------- translation of sentences --------------------------------
---------------------------- function definitions ---------------------------

transMatch :: IsaSign.Sign -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds 
           -> Result (Named Sentence) 
transMatch sign t = case (t, constTab sign) of 
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _,
   cs) -> 
         let df = showIsaName nm 
             tx = transExp cs x
             y = maybe (noType) id $ Map.lookup df cs 
         in return $ makeSentence df cs y df ps tx
  _ -> fail "Haskell2IsabelleHOLCF.transMatch, case not supported"


------------------------------- translates instances ---------------------------------

transIMatch :: IsaSign.Sign -> HsType -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds 
            -> Result (Named Sentence) 
transIMatch sign t s
  = case (s, constTab sign) of 
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody ex) _,
   ct) -> 
         let tx = transExp ct ex
             df = showIsaName nm
             c = transClass $ getInstClass t           -- instantiated class
             x = transType [] $ getInstType t          -- instatiating type
             w = maybe [] id $ Map.lookup (typeId x) (arities $ tsig sign)  -- all arities of inst. type 
             cs = maybe [] id $ Map.lookup c (Map.fromList w)  -- selects the arity for the inst. class
             ndf = (typeId x) ++ "_" ++ df
             ty = maybe (noType) id $ Map.lookup df ct -- abstract method type
             nty = repVarClass ty c (constrVarClass x cs)  -- in ty, replaces the variable of class c with type x, constraining variables in x with cs
             in return $ makeSentence ndf ct nty df ps tx 
  _ -> fail "Haskell2IsabelleHOLCF.transIMatch, case not supported"


------------------------------ Signature translation -----------------------------

transSignature :: HatAna.Sign -> Result IsaSign.Sign
transSignature sign = Result [] $ Just $ IsaSign.emptySign
  { baseSig = HsHOLCF_thy,
    tsig = emptyTypeSig 
           { 
             classrel = getClassrel (HatAna.types sign),
             abbrs = getAbbrs (HatAna.types sign),
             arities = -- trace (show (HatAna.instances sign)) $ 
                    getArities (HatAna.instances sign) 
           },
    constTab = getConstTab (HatAna.values sign),
    domainTab = getDomainTab (HatAna.values sign)
  }

------------------------------ translation of types -------------------------------
{- This signature translation takes after the one to Stratego, and relies on 
 Isabelle.Translation to solve naming conflicts. -}

transType :: [HsType] -> HsType -> IsaType
transType c t = maybe noType id $ transMType c t

transMType :: [HsType] -> HsType -> Maybe IsaType
transMType c (Typ t) = transT (transIdV c) transIdC (transMType c) t

transT :: Show d => (PNT -> Maybe IsaType) -> (PNT -> Maybe IsaType) -> (d -> Maybe IsaType) -> 
                    HsTypeStruct.TI PNT d -> Maybe IsaType
transT trIdV trIdC trT t =
 case mapTI3 trIdV trIdC trT t of    
    Just (HsTyFun t1 t2) -> return $ IsaSign.mkContFun t1 t2
    Just (HsTyApp t1 t2) -> return $ IsaSign.typeAppl t1 [t2]
    Just (HsTyVar a) -> return a
    Just (HsTyCon k) -> return k 
    _ -> Nothing
--    _ -> not_supported "Type" t

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
           in if u == v then k:s else s       
--           in if u == v && k /= IsaClass "Eq" && k /= IsaClass "Ord" then k:s else s                  

transIdV :: [HsType] -> PNT -> Maybe IsaType
transIdV c t = return $ TFree (showIsaName t) (getSort c t)

transIdC :: PNT -> Maybe IsaType
transIdC t = case t of
 PNT _ (TypedIds.Class _) _ -> Nothing
 _ -> return $ let tfs = transFields t
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

mapTI3 :: (i1 -> Maybe i2) -> 
          (i1 -> Maybe i2) -> 
          (t1 -> Maybe t2) -> 
          TI i1 t1 -> Maybe (TI i2 t2)
mapTI3 vf cf tf ty = case ty of
     HsTyFun x y        -> do a <- tf x
                              b <- tf y
                              return $ HsTyFun a b
     HsTyApp f x        -> do a <- tf f
                              b <- tf x
                              return $ HsTyApp a b
     HsTyVar nm         -> do a <- vf nm  
                              return $ HsTyVar a
     HsTyCon nm         -> do a <- cf nm
                              return $ HsTyCon a
     _ -> Nothing
--     HsTyForall xs ps t -> HsTyForall (map vf xs) (map tf ps) (tf t)

-- error :: forall a. [Char] -> a
-- not_supported :: (Show t, Show i) => String -> HsTypeStruct.TI i t -> a
-- not_supported s x = error $ s++" Haskell2IsabelleHOLCF.transT, type not supported: "++show x

------------------------------ Class translation ------------------------------

mkIsaClass :: CName -> IsaClass
mkIsaClass n = IsaClass n

transClass :: HsType -> IsaClass
transClass x = case x of 
    Typ (HsTyCon c) -> IsaClass (showIsaName c)
    Typ _ -> error "Hs2HOLCF.transClass"
-- need check of parameters?

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

------------------------------- SIGN fields translation ---------------------------------
------------------------------- translation for ConstTab --------------------------

getConstTab ::  VaMap -> ConstTab
getConstTab f = Map.map fst (Map.filter (\x -> (snd x) == IsaVal) (getAConstTab f))  

getAConstTab ::  VaMap -> AConstTab
getAConstTab f =   
    liftMapByListD Map.toList Map.fromList (showIsaName . fst) 
         (\y -> (transMScheme $ snd y, getValInfo $ fst y)) nothingFiOut f

getValInfo :: HsId -> IsaVT
getValInfo n = case n of 
   HsCon _ -> IsaConst
   _ -> IsaVal

transMScheme :: HsScheme -> Maybe IsaType
transMScheme s = case s of 
    Forall _ _ (c TiTypes.:=> t) -> transMType c t
--    _ -> Nothing

transScheme :: HsScheme -> IsaType
transScheme s = maybe (error "HsHOLCF, transScheme") id $ transMScheme s


----------------------------- translation for Classrel (from KEnv) -----------------------

getClassrel :: TyMap -> IsaSign.Classrel
getClassrel f = 
     liftMapByList Map.toList Map.fromList (mkIsaClass . showIsaName) transClassInfo f

transClassInfo :: (Kind, HsTypeInfo) -> Maybe [IsaClass]
transClassInfo p = case snd p of 
        TiTypes.Class _ _ _ _ -> Just (map transClass (extClassInfo $ snd p))
        _ -> Nothing 

------------------------- translation of Abbrs (from KEnv) -----------------------------
 
getAbbrs ::  TyMap -> IsaSign.Abbrs
getAbbrs f = let 
 mf = liftMapByList Map.toList Map.fromList showIsaName transAbbrsInfo f
 nf = Map.filter (\x -> case x of 
        Just _ -> True  
        Nothing -> False) mf
 in Map.map (\x -> maybe ([],noType) id x) nf

transAbbrsInfo :: (Kind, HsTypeInfo) -> Maybe ([TName], IsaType)
transAbbrsInfo p = case (snd p) of 
  TiTypes.Synonym _ _ -> let x = extAbbrsInfo (snd p) in
                      return $ (map showIsaName (fst x), transType [] (snd x))
  _ -> Nothing

---------------------------- translation of arities --------------------------------

getArities :: HsInstances -> IsaSign.Arities
getArities db = -- trace (show $ getTypeInsts db) $ trace (show db) $ 
      Map.fromList (groupInst $ getTypeInsts db) -- \$ getIsaInsts db  

getTypeInsts :: HsInstances -> [IsaTypeInsts]
getTypeInsts db = [(typeId $ transType [] $ getMainInstType x, [transInst x]) | x <- db]

transInst :: HsInstance -> (IsaClass, [(IsaType, [IsaClass])])
transInst i = let x = prepInst i in 
         (transClass $ fst x, reverse [(transType [] a, map transClass b) | (a,b) <- snd x])

------------------------------ translation of domaintab ---------------------------

getDomainTab :: VaMap -> IsaSign.DomainTab 
getDomainTab f =  
   getDepDoms $ remove_duplicates 
          [getDomainEntry (getAConstTab f) x | x <- Map.keys f, checkTyCons x]

getDomainEntry :: AConstTab -> HsId -> [IsaSign.DomainEntry]
getDomainEntry ctab t = case t of
  HsCon (PNT _ (TypedIds.ConstrOf _ d) _) -> 
     [(getDomType ctab (showIsaName t), [(b, getFieldTypes ctab b) | 
            b <- [showIsaName c | (PN c _) <- map conName (constructors d)]])]
  _ -> []

--------------------------------- Term translation -------------------------------
-------------------------------------------- term and patterns ------------------------

transExp :: ConstTab -> PrExp -> IsaTerm
transExp c t = maybe xDummy id $ transMExp c t

transPat :: ConstTab -> PrPat -> IsaPattern
transPat c t = maybe xDummy id $ transMPat c t

transMExp :: ConstTab -> PrExp -> Maybe IsaTerm
transMExp cs t = case t of 
    (TiPropDecorate.Exp e) -> case e of
       HsLit _ (HsInt n) -> return $ 
           Const ("(Def (" ++ (show n) ++ "::int))") (IsaSign.Type "int lift" [] [])
       HsLet (TiPropDecorate.Decs ds _) k -> do
          w <- mapM (transPatBind cs) ds
          z <- transMExp cs k
          return $ Let w z -- (transE showIsaName (transExp cs) (transPat cs) e) 
       _ -> transE showIsaName (transMExp cs) (transMPat cs) e
    TiPropDecorate.TiSpec w s _ -> case w of 
       HsVar x -> transHV s x
       HsCon x -> transCN s x
    TiPropDecorate.TiTyped x _ -> transMExp cs x

transPatBind :: ConstTab -> PrDecl -> Maybe (IsaTerm,IsaTerm)
transPatBind cs s = case s of
  TiPropDecorate.Dec (PropSyntaxStruct.Base 
        (HsDeclStruct.HsPatBind _ p (HsGuardsStruct.HsBody e) _)) -> do
              x <- transMPat cs p
              y <- transMExp cs e
              return (x, y) 
  _ -> error "HsHOLCF, transPatBind"

transMPat :: ConstTab -> PrPat -> Maybe IsaPattern
transMPat cs t = case t of 
    TiDecorate.Pat p -> transP showIsaName (transMPat cs) p
    TiDecorate.TiPSpec w s _ -> case w of 
         HsVar x -> transHV s x
         HsCon x -> transCN s x
    TiDecorate.TiPTyped x _ -> transMPat cs x
    _ -> return $ Bottom

transE :: (PNT -> VName) -> (e -> Maybe IsaTerm) -> (p -> Maybe IsaPattern) -> 
            (HsExpStruct.EI PNT e p j h k) -> Maybe IsaTerm
transE trId trE trP e =
 case (mapEI5 trId trE trP e) of 
   Just (HsId (HsVar _))              -> return $ Const "DIC" noType     
   Just (HsApp x y)                   -> return $ termMAppl IsCont x [y]  
   Just (HsLambda ps x)               -> return $ termMAbs IsCont ps x 
   Just (HsIf x y z)                  -> return $ If x y z IsCont 
   Just (HsTuple xs)                  -> return $ Tuplex xs IsCont 
   Just (HsParen x)                   -> return $ Paren x
   _ -> Nothing -- Const "dummy" noType
--   _ -> error "Haskell2IsabelleHOLCF.transE, not supported"
--   HsId (HsCon c)              -> Const c noType
--   HsId (HsVar "==")              -> Const "Eq" noType     
--   HsLet ds e                  -> Let (map transPatBind ds) (transExp e) 
--   HsCase e ds                 -> Case e ds 
 
transP :: IsaName i => (i -> VName) -> (p -> Maybe IsaPattern) -> 
            (HsPatStruct.PI i p) -> Maybe IsaPattern
transP trId trP p =
 case mapPI3 trId trP p of
   Just (HsPId (HsVar _)) -> return $ Const "DIC" noType
   Just (HsPTuple _ xs) -> return $ Tuplex xs IsCont 
   Just (HsPParen x) -> return $ Paren x
   Just HsPWildCard -> return $ Wildcard
   _ -> Nothing -- error "Haskell2IsabelleHOLCF.transP, not supported"
--   HsPList ps -> plist ps
--   HsPId (HsCon c) -> Const c noType
--   HsPLit _ lit -> litPat (transL lit) -- new
--   HsPApp c ps -> App x y IsCont
--   HsPAsPat x p -> AsPattern (x,p)
--   HsPIrrPat p -> twiddlePat p

transCN :: HsScheme -> PNT -> Maybe IsaTerm
transCN s x = let 
  y = showIsaName x
  z = transScheme s 
  f w = Const w z
  in return $
  if elem pcpo (typeSort z) then case pp x of
      "True" -> f "TT"
      "False" -> f "FF"
      _ -> f y
  else f y

transHV :: HsScheme -> PNT -> Maybe IsaTerm
transHV s x = let 
      n = showIsaName x 
      k = transScheme s
      tag = elem pcpo (typeSort k)
      qq = pp x
   in if qq == "error" then Nothing else return $
   case qq of  
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


---------------------------------- auxiliary ------------------------------------------------

class IsaName i => TransFunction i j k where
 transFun :: (j i) -> k

mapEI5 :: (i1 -> i2) -> 
          (e1 -> Maybe e2) ->
          (p1 -> Maybe p2) ->
          EI i1 e1 p1 d t c ->
          Maybe (EI i2 e2 p2 d t c)
mapEI5 vf ef pf exp =
  case exp of
    HsId n                 -> return $ HsId (HsIdent.mapHsIdent2 vf vf n)
    HsApp x y              -> do a <- ef x
                                 b <- ef y
                                 return $ HsApp a b
    HsLambda ps e          -> do xs <- mapM pf ps
                                 y <- ef e
                                 return $ HsLambda xs y
    HsIf x y z             -> do a <- ef x
                                 b <- ef y
                                 c <- ef z
                                 return $ HsIf a b c
    HsTuple xs             -> do zs <- mapM ef xs
                                 return $ HsTuple zs
    HsParen x              -> do a <- ef x
                                 return $ HsParen a 
    _                      -> Nothing
--    HsLit s l              -> HsLit s l
--    HsInfixApp x op z      -> HsInfixApp (ef x) (mapHsIdent2 vf cf op) (ef z)
--    HsNegApp s x           -> HsNegApp s (ef x)  
--    HsLet ds e             -> HsLet (df ds) (ef e)
--    HsCase e alts          -> HsCase (ef e) (map (mapAlt ef pf df) alts) 
--    HsDo stmts             -> HsDo (mStmt stmts)
--    HsList xs              -> HsList (map ef xs)
--    HsLeftSection x op     -> HsLeftSection (ef x) (mapHsIdent2 vf cf op)
--    HsRightSection op y    -> HsRightSection (mapHsIdent2 vf cf op) (ef y) 
--    HsRecConstr s n upds   -> HsRecConstr s (cf n) (mapFieldsI vf ef upds)
--    HsRecUpdate s e upds   -> HsRecUpdate s (ef e) (mapFieldsI vf ef upds)
--    HsEnumFrom x           -> HsEnumFrom (ef x) 
--    HsEnumFromTo x y       -> HsEnumFromTo (ef x) (ef y) 
--    HsEnumFromThen x y     -> HsEnumFromThen (ef x) (ef y) 
--    HsEnumFromThenTo x y z -> HsEnumFromThenTo (ef x) (ef y) (ef z)
--    HsListComp stmts       -> HsListComp (mStmt stmts)
--    HsExpTypeSig s e c t   -> HsExpTypeSig s (ef e) (ctxf c) (tf t)
--    HsAsPat n e            -> HsAsPat (vf n) (ef e)  -- pattern only
--    HsWildCard             -> HsWildCard        -- ditto
--    HsIrrPat e             -> HsIrrPat (ef e)   -- ditto
--  where
--    mStmt = mapStmt ef pf df

mapPI3 :: 
          (i1 -> i2) ->
          (p1 -> Maybe p2) ->
          PI i1 p1 -> Maybe (PI i2 p2)
mapPI3 vf pf pat =
  case pat of
    HsPId n                -> return $ HsPId (HsIdent.mapHsIdent2 vf vf n)
    HsPLit s l             -> return $ HsPLit s l
    HsPTuple s ps          -> do bs <- mapM pf ps
                                 return $ HsPTuple s bs
    HsPParen p             -> do h <- pf p
                                 return $ HsPParen h 
    HsPWildCard            -> return $ HsPWildCard
    _                      -> Nothing 
--    HsPNeg s l             -> HsPNeg s l
--    HsPSucc s n l          -> HsPSucc s (vf n) l
--    HsPInfixApp x op y     -> HsPInfixApp (pf x) (cf op) (pf y)
--    HsPApp nm ps           -> HsPApp (cf nm) (map pf ps)
--    HsPList  s ps          -> HsPList s (map pf ps)
--    HsPRec nm fields       -> HsPRec (cf nm) (mapFieldsI vf pf fields)
--    HsPAsPat nm p          -> HsPAsPat (vf nm) (pf p)
--    HsPIrrPat p            -> HsPIrrPat (pf p)


