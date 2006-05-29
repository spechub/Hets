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
import Monad

import TypedIds

import TiTypes
import TiKinds
 
import PNT 
import UniqueNames

import SyntaxRec
import TiPropDecorate
import PropSyntaxStruct
import HsDeclStruct
import HsGuardsStruct
import TiDecorate

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts as IsaConsts

------------------------------ Top level function ------------------------------
transTheory :: Continuity -> Bool -> 
  HatAna.Sign -> [Named PrDecl] -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transTheory c m sign sens = do 
  sign' <- -- trace (showL (HatAna.instances sign)) $ 
             transSignature c m sign
  (sign'',sens'') <- transSentences c sign' (map sentence sens)
  return (sign'', sens'')

------------------------------ Theory translation -------------------------------
{- Relevant theories in Programatica: base/Ti/TiClasses (for 
tcTopDecls); property/parse2/Parse/PropPosSyntax (def of HsDecl).  -}

data ExpRole = FunDef | InstDef | PLogic

transSentences :: Continuity -> 
    IsaSign.Sign -> [PrDecl] -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transSentences c sign ls =  do 
                            xx0 <- mapM (transSentence c sign FunDef) ls
                            xx <- return $ removeEL xx0 
                            xs <- return [[s] | [s] <- xx, extAxType s /= noType]
                            ys <- return $ fixMRec c xs
                            ac <- return $ newConstTab c ys
                            nc <- return $ Map.union (constTab sign) ac
                            nsig <- -- trace (showL $ Map.toList nc) $ 
                                    -- trace (showL ls) $ 
                                     return $ sign {constTab = nc}
                            zz0 <- trace (showL $ Map.toList $ arities $ tsig nsig) $ mapM (transSentence c nsig InstDef) ls
                            zz <- return $ removeEL zz0
                            zw <- return $ concat zz
                            zs <- return [s | s <- zw, not $ 
                                   elem (getTermName $ extRightH s)
                                    ["DollarXMinusXMinusXSlashXEqX",
                                      "DollarXMinusXMinusXEqXEqX"]]
                            return (nsig, ys ++ zs) 

transSentence :: Continuity -> 
      IsaSign.Sign -> ExpRole -> PrDecl -> Result [Named IsaSign.Sentence]
transSentence c sign a (TiPropDecorate.Dec d) = case d of
  PropSyntaxStruct.Base p -> case (a,p) of
    (FunDef,  HsDeclStruct.HsFunBind _ ws) -> do  
          k <- case ws of 
                  [x] -> transMatch c sign x
                  _ -> transMMatch c sign ws
          return [k]  
    (InstDef, HsInstDecl _ _ _ t (TiPropDecorate.Decs ds _)) -> do
        q <- mapM (transIMatch c sign t) 
             [y | TiPropDecorate.Dec (PropSyntaxStruct.Base 
                               (HsDeclStruct.HsFunBind _ [y])) <- ds]  
        return q 
    _ -> return []
  _ -> return []


makeSentence :: Continuity -> 
  String -> IsaType -> VName -> [IsaPattern] -> IsaTerm -> Named Sentence
makeSentence a d y df ps tx = 
  if tx == xDummy then NamedSen d True False $ ConstDef $ IsaEq xDummy $ xDummy 
  else NamedSen d True False $ ConstDef $
       IsaEq (Const df y) $ termMAbs a ps tx

--------------------------- translation of sentences -----------------------------
---------------------------- function definitions ---------------------------

transMatch :: Continuity -> 
        IsaSign.Sign -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds 
           -> Result (Named Sentence) 
transMatch c sign t = case (t, constTab sign) of 
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _,
   cs) -> 
         let df = mkVName $ showIsaName nm 
             tx = transExp c cs x
             y = maybe (noType) id $ Map.lookup df cs 
             qs = map (transPat c cs) ps
         in return $ makeSentence c (IsaSign.orig df) y df qs tx
  _ -> fail "Haskell2IsabelleHOLCF.transMatch, case not supported"


------------------------ translate pattern matching definitions ---------------------

-- Main function. transMultiDef translate the expressions, 
-- formCaseExp builds the case expression.
transMMatch :: Continuity -> 
        IsaSign.Sign -> [HsDeclStruct.HsMatchI PNT PrExp PrPat ds] 
           -> Result (Named Sentence)
transMMatch c sign ds = case ds of 
   [] -> error "transMMatch, Hs2HOLCF"
   a:as -> let 
      a1 = extInfo a
      cs = constTab sign
      df = mkVName $ showIsaName $ fst a1 
      ls = map (snd . extInfo) ds
      ww = transMultiDef c cs ls
      tx = -- trace ("transMultiDef output " ++ showL ww) $ 
           formCaseExp c ww 
      y = maybe (noType) id $ Map.lookup df cs  
      bs = fst $ snd a1
      qs = reverse $ mkVVs (length bs)
    in return $ makeSentence c (IsaSign.orig df) y df qs tx
 where  
   extInfo (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _) = (nm,(ps,x)) 
   mkVVs n = if 0 < n 
     then (Free (mkVName $ "qX" ++ (show n)) noType):(mkVVs (n-1)) else []

-- annotated translation function. To each parameter pattern - IsaPattern - 
-- is associated 
-- datatype information - [(String,Int)]
-- case variable name - IsaTerm
-- parameter name before translation - String 
transMultiDef :: Continuity -> 
        ConstTab -> [([PrPat],PrExp)] -> 
                   [([([(String,Int)],((IsaTerm,String),IsaPattern))],IsaTerm)] 
transMultiDef c sign ls = -- trace ("\n multiDef" ++ showL ls) $ 
  let 
   ws = -- trace ("\n csAris input " ++ (showL $ concat $ map fst ls)) $ 
        csAris [fst w | w <- ls]
   ks = -- addDefault $ trace ("\n csAris result " ++ showL ws) $ 
        [([newInfo c sign v | v <- xs], transExp c sign y) | (xs,y) <- ls]
   ss = -- trace ("\n transMultiDef inter " ++ showL ks) $ 
        map standizeVars ks 
 in -- trace ("\n summary ws " ++ (showL ws) ++ "\n summary ss " ++ showL ss) $ 
    [(zipNE ws rs, s) | (rs,s) <- ss]
 where
  newInfo c sign f = (snd $ extCI f, transPat c sign f)
  zipNE ws rs = case ws of 
    [] -> []
    []:xs -> zipNE xs (tail rs)
    _ -> (head ws,head rs):(zipNE (tail ws) $ tail rs)

-- Extract datatype information from a list of patterned parameter lists.
-- Returns the list of constructors and arities for the parameter datatypes.  
csAris :: [[PrPat]] -> [[(String,Int)]] 
csAris ls = case ls of 
 [] -> error "formCaseExp, Hs2HOLCF"
 m:ms -> case m of
  [] -> []
  h:hs -> let 
    w = csAris [tail a | a <- ls]
   in (extCL (map head ls)) : w 

-- Standardizes parameter names from all the expressions.
-- Associates a case variable name. 
standizeVars :: ([(String,IsaPattern)],IsaTerm) -> 
         ([((IsaTerm,String),IsaPattern)],IsaTerm)
standizeVars k = let
   i = length $ fst k
 in stdVars k i 
 where
 stdVars k i = case fst k of 
    [] -> ([], snd k) 
    a:as -> let 
       j = length as
       n = i - j
       na = sbVs (snd a, n) 
       h = mkVs n
       nk = renVars na [(snd a)] $ snd k
       y = stdVars (as,nk) i
     in (((h, fst a), na):(fst y), snd y)
 sbVs a = case (fst a) of 
    Free _ _ -> mkVs (snd a)
    Wildcard -> mkVs (snd a)
    _ -> fst a
  
mkVs :: Int -> IsaTerm
mkVs n = Free (mkVName $ "qX" ++ (show n)) noType

-- Forms the nested case expression, using trCase. 
formCaseExp :: Continuity -> 
   [([([(String,Int)],((IsaTerm,String),IsaPattern))],IsaTerm)] -> IsaTerm 
formCaseExp ct ls = 
 case ls of 
 [] -> error "formCaseExp, Hs2HOLCF"
 (m:ms) -> case fst m of  -- m::([([(String,Int)],((IsaTerm,String),IsaPattern))],IsaTerm)
   [] -> snd m
   h:hs -> let -- h:: ([(String,Int)],((IsaTerm,String),IsaPattern)) 
      k1s = map fst ls 
      xs = map head k1s  -- :: [([(String,Int)],((IsaTerm,String),IsaPattern))]
      xxs = -- trace ("\n formCaseExp inter xs " ++ showL xs) $ 
            remove_duplicates [((snd $ fst $ snd x, snd $ snd x), 
                [(us,t) | (u:us,t) <- ls, u == x] ++ 
                     [(us,t) | ((_,(_,Free _ _)):us,t) <- ls]) | x <- xs]
      ws = -- trace ("\n formCaseExp inter xxs first " ++ (showL (map (fst . fst) xxs)) ++ "\n formCaseExp inter xxs sec " ++ (showL (map (snd . fst) xxs)) ++ "\n formCaseExp inter xxs thd " ++ (showL (map snd xxs))) $
           remove_duplicates $ [((a,b),formCaseExp ct c) | ((a,b),c) <- xxs] 
    in makeCase (fst $ fst $ snd h) $ map (\z -> trCase ct z ws) (fst h)                
 where
  makeCase t ls = Case t ls 

------------------------------- translates instances ---------------------------------

transIMatch :: Continuity -> 
     IsaSign.Sign -> HsType -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds 
            -> Result (Named Sentence) 
transIMatch a sign t s
  = case (s, constTab sign) of 
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody ex) _,
   ct) -> 
         let tx = transExp a ct ex
             df = if pp nm == "==" then mkVName "hEq" 
                  else if pp nm == "/=" then mkVName "hNEq"
                  else mkVName $ showIsaName nm
             c = transClass $ getInstClass t           -- instantiated class
             x = transType a [] $ getInstType t          -- instatiating type
             w = maybe [] id $ Map.lookup (typeId x) (arities $ tsig sign)  
                                                  -- all arities of inst. type 
             cs = maybe [] id $ Map.lookup c (Map.fromList w)  
                                      -- selects the arity for the inst. class
             ndf = typeId x ++ "_" ++ IsaSign.orig df
             ty = maybe (noType) id $ Map.lookup df ct -- abstract method type
             nty = repVarClass ty c (constrVarClass x cs)  
             qs = map (transPat a ct) ps
                        -- in ty, replaces the variable of class c with type x,
                        -- constraining variables in x with cs
             tst = makeSentence a ndf nty df qs tx 
             in return tst 
  _ -> fail "Haskell2IsabelleHOLCF.transIMatch, case not supported"


------------------------------ Signature translation -----------------------------

transSignature :: Continuity -> Bool -> HatAna.Sign -> Result IsaSign.Sign
transSignature c m sign =  let -- trace ("HatAna instances " ++ showL $ HatAna.instances sign) $ 
 xx = getDomainTab c (HatAna.values sign)
 in Result [] $ Just $ IsaSign.emptySign 
  { baseSig = case (c,m) of 
                   (IsCont,False) -> HsHOLCF_thy
                   (NotCont,False) -> HsHOL_thy
                   (IsCont,True) -> MHsHOLCF_thy
                   (NotCont,True) -> MHsHOL_thy,
    tsig = emptyTypeSig 
           { 
             classrel = getClassrel c (HatAna.types sign),
             abbrs = getAbbrs c (HatAna.types sign),
             arities = getArities c xx (HatAna.instances sign) 
           },
    constTab =  getConstTab c (HatAna.values sign),
    domainTab = xx
  }

------------------------------ translation of types -------------------------------
{- This signature translation takes after the one to Stratego, and relies on 
 Isabelle.Translation to solve naming conflicts. -}

transType :: Continuity -> [HsType] -> HsType -> IsaType
transType a c t = maybe noType id $ transMType a c t

transMType :: Continuity -> [HsType] -> HsType -> Maybe IsaType
transMType a c (Typ t) = transT a 
        (transIdV a c) (transIdC a) (transMType a c) t

transT :: Show d => Continuity -> (PNT -> Maybe IsaType) -> 
               (PNT -> Maybe IsaType) -> (d -> Maybe IsaType) -> 
                    TI PNT d -> Maybe IsaType
transT c trIdV trIdC trT t =
 case mapTI3 trIdV trIdC trT t of    
    Just (HsTyFun t1 t2) -> return $ (case c of 
              IsCont -> mkContFun t1 t2
              NotCont -> mkFunType t1 t2)
    Just (HsTyApp t1 t2) -> case t1 of 
         IsaSign.Type name s args -> -- better resolve nested HsTyApp first
                    return $ IsaSign.Type name s $ args ++ [t2] 
         _ -> Nothing
    Just (HsTyVar a) -> return a
    Just (HsTyCon k) -> return k 
    _ -> Nothing

getSort :: Continuity -> [HsType] -> PNT -> IsaSort
getSort r c t = case c of 
   [] -> case r of 
             IsCont -> dom
             NotCont -> holType
   x:cs -> let a = getInstType x 
               b = getInstClass x
               d = getLitName a
               s = getSort r cs t
               k = transClass b
               u = showIsaName d
               v = showIsaName t
           in if u == v then k:s else s       

transIdV :: Continuity -> [HsType] -> PNT -> Maybe IsaType
transIdV a c t = return $ TFree (showIsaName t) (getSort a c t)

transIdC :: Continuity -> PNT -> Maybe IsaType
transIdC c t = case t of
 PNT _ (TypedIds.Class _ _) _ -> Nothing
 _ -> return $ let 
    tfs = transFields c t
    srt = case c of 
             IsCont -> dom
             NotCont -> holType      
  in 
  case (UniqueNames.orig t) of 
    UniqueNames.G (PlainModule m) n _ -> 
                  IsaSign.Type (transTN c m n) srt tfs 
    UniqueNames.G (MainModule m) n _ -> IsaSign.Type (transPath m n) srt tfs 
    _ -> IsaSign.Type (showIsaName t) srt tfs

transFields ::  Continuity -> PNT -> [IsaType] 
transFields c t = let 
     srt = case c of 
             IsCont -> dom
             NotCont -> holType      
  in case t of 
    PNT _ (TypedIds.Type q) _ -> 
          [TFree (showIsaS x) srt | (PN x _) <- TypedIds.fields q]
    PNT _ (TypedIds.FieldOf _ q) _ -> 
          [TFree (showIsaS x) srt | (PN x _) <- TypedIds.fields q]
    _ -> []

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

{- mkIsaClass :: CName -> IsaClass
mkIsaClass n = IsaClass n -}

transClass :: HsType -> IsaClass
transClass x = case x of 
    Typ (HsTyCon c) -> IsaClass (showIsaName c)
    Typ _ -> error "Hs2HOLCF.transClass"
-- need check of parameters?

------------------------------- Kind translation ------------------------------

----------- Kinds

data IsaExKind = IKind IsaKind | IClass | IsaPLogic

data IsaKind  = Star
              | IsaKfun IsaKind IsaKind
                deriving (Ord, Eq, Show)

kindTrans :: Kind -> IsaKind
kindTrans x = case x of 
                 K Kstar -> Star
                 K (Kfun a b) -> IsaKfun (kindTrans a) (kindTrans b)
                 _ -> error "error, Hs2HOLCF.kindTrans,"

kindExTrans :: Kind -> IsaExKind
kindExTrans x = case x of 
                 K Kstar -> IKind Star
                 K (Kfun a b) -> IKind (IsaKfun (kindTrans a) (kindTrans b))
                 K Kpred -> IClass
                 K Kprop -> IsaPLogic
                 _ -> error "Hs2HOLCF.kindExTrans, kind variables not supported"

------------------------------- SIGN fields translation ----------------------------
------------------------------- translation for ConstTab --------------------------

getConstTab ::  Continuity -> VaMap -> ConstTab
getConstTab c f = Map.map fst (Map.filter (\x -> (snd x) == IsaVal) 
            (getAConstTab c f))  

getAConstTab ::  Continuity -> VaMap -> AConstTab
getAConstTab c f =   
    liftMapByListD Map.toList Map.fromList (mkVName . showIsaName . fst) 
         (\y -> (transMScheme c $ snd y, getValInfo $ fst y)) nothingFiOut f

getValInfo :: HsId -> IsaVT
getValInfo n = case n of 
   HsCon _ -> IsaConst
   _ -> IsaVal

transMScheme :: Continuity -> HsScheme -> Maybe IsaType
transMScheme a s = case s of 
    Forall _ _ (c TiTypes.:=> t) -> transMType a c t

transScheme :: Continuity -> HsScheme -> IsaType
transScheme c s = maybe (error "HsHOLCF, transScheme") id $ transMScheme c s


----------------------------- translation for Classrel (from KEnv) ---------------

getClassrel :: Continuity -> TyMap -> IsaSign.Classrel
getClassrel c f = 
     liftMapByList Map.toList Map.fromList (IsaClass . showIsaName) (transClassInfo c) f

transClassInfo :: Continuity -> (Kind, HsTypeInfo) -> Maybe [IsaClass]
transClassInfo c p = case snd p of 
  TiTypes.Class _ _ _ _ -> 
    Just $ remove_duplicates $ (case c of 
                       IsCont -> dom 
                       NotCont -> holType) ++ (map transClass (extClassInfo $ snd p))
  _ -> Nothing 

------------------------- translation of Abbrs (from KEnv) -----------------------
 
getAbbrs ::  Continuity -> TyMap -> IsaSign.Abbrs
getAbbrs c f = let 
 mf = liftMapByList Map.toList Map.fromList showIsaName (transAbbrsInfo c) f
 nf = Map.filter (\x -> case x of 
        Just _ -> True  
        Nothing -> False) mf
 in Map.map (\x -> maybe ([],noType) id x) nf

transAbbrsInfo :: Continuity -> (Kind, HsTypeInfo) -> Maybe ([TName], IsaType)
transAbbrsInfo c p = case (snd p) of 
  TiTypes.Synonym _ _ -> let x = extAbbrsInfo (snd p) in
                      return $ (map showIsaName (fst x), transType c [] (snd x))
  _ -> Nothing

---------------------------- translation of arities --------------------------------

getArities :: Continuity -> DomainTab -> HsInstances -> IsaSign.Arities
getArities c dt db = trace (showL db) $ 
      Map.fromList (groupInst $ getTypeInsts c dt db) -- \$ getIsaInsts db  

getTypeInsts :: Continuity -> DomainTab -> HsInstances -> [IsaTypeInsts]
getTypeInsts c dt db = [(typeId $ transType c [] $ getMainInstType x, 
                          [transInst c x]) | x <- db]
                         ++ [(u,[(IsaClass "Eq", [])]) | [(IsaSign.Type u v [],_)] <- dt]

transInst :: Continuity -> HsInstance -> (IsaClass, [(IsaType, [IsaClass])])
transInst c i = let x = prepInst i 
                    w = case c of 
                         IsCont -> pcpo
                         NotCont -> isaTerm
  in (transClass $ fst x, 
     reverse [(transType c [] a, w:map transClass b) | (a,b) <- snd x])

------------------------------ translation of domaintab ---------------------------

getDomainTab :: Continuity -> VaMap -> IsaSign.DomainTab 
getDomainTab c f =  let 
  ls = remove_duplicates 
     [getDomainEntry (getAConstTab c f) x | x <- Map.keys f, checkTyCons x]
  in -- trace (showL $ Map.keys f) $ 
      reverse $ getDepDoms ls

getDomainEntry :: AConstTab -> HsId -> [IsaSign.DomainEntry]
getDomainEntry ctab t = case t of
  HsCon (PNT _ (TypedIds.ConstrOf _ d) _) -> 
     [(getDomType ctab (mkVName $ showIsaName t), [(b, getFieldTypes ctab b)
         | b <- [ mkVName $ showIsaName c 
                   | PN c _ <-  map conName (constructors d)]])]
  _ -> []

--------------------------------- Term translation -------------------------------
-------------------------------------------- term and patterns -------------------

transExp :: Continuity -> ConstTab -> PrExp -> IsaTerm
transExp a c t = maybe xDummy id $ transMExp a c t

transPat :: Continuity -> ConstTab -> PrPat -> IsaPattern
transPat a c t = maybe xDummy id $ transMPat a c t

transMExp :: Continuity -> ConstTab -> PrExp -> Maybe IsaTerm
transMExp a cs t = case t of 
    (TiPropDecorate.Exp e) -> case e of
       HsLit _ (HsInt n) -> return $ case a of
           IsCont -> 
              Const (mkVName $ "(Def (" ++ show n ++ "::int))") 
                     (IsaSign.Type "dInt" [] [])
           NotCont -> 
              Const (mkVName $ "(" ++ show n ++ "::int)") 
                     (IsaSign.Type "int" [] [])
       HsLit _ (HsFloatPrim n) -> return $ case a of
           IsCont -> 
              Const (mkVName $ "(Def (" ++ show n ++ "::Rat))") 
                     (IsaSign.Type "dRat" [] [])
           NotCont -> 
              Const (mkVName $ "(" ++ show n ++ "::Rat)") 
                     (IsaSign.Type "Rat" [] [])
       HsList xs -> return $ case xs of 
          [] -> case a of 
                   IsCont -> conDouble "lNil"
                   NotCont -> conDouble "[]"
          _ -> error "Hs2HOLCF, transMExp, unsupported list notation" 
       HsLet (TiPropDecorate.Decs ds _) k -> do
          w <- mapM (transPatBind a cs) ds
          z <- transMExp a cs k
          return $ Let w z
       HsCase e as -> do e1 <- transMExp a cs e
                         bs <- transCases a cs (map extPE as) -- mapM (transCasePt a cs) as 
                         return -- traceL [show e, show e1, showL as, showL bs] 
                                   $ Case e1 bs
       _ -> transE a (mkVName . showIsaName) (transMExp a cs) (transMPat a cs) e
    TiPropDecorate.TiSpec w s _ -> case w of 
       HsVar x -> transHV a s x
       HsCon x -> transCN a s x
    TiPropDecorate.TiTyped x _ -> transMExp a cs x
    _                      -> Nothing 

transCases :: Continuity -> ConstTab -> -- [PNT.PName] -> 
     [(TiPat PNT, TiPropDecorate.TiExp PNT)] -> Maybe [(IsaTerm,IsaTerm)]
transCases r cs ks = case ks of 
 [] -> return []
 x:xs -> let 
     cnn = extCL $ map fst ks -- (cons, arity) list for the case value.
     ys = [((snd $ extCI f, transPat r cs f), transExp r cs g) 
                             | (f,g) <- ks] -- (cons, (ptn, exp)) list.
  in if cnn == [] then error "Hs2HOLCF, transCases - case expression not allowed"   
       else return $ map (\h -> trCase r h ys) cnn 
  
extPE :: HsGuardsStruct.HsAlt (TiPropDecorate.TiExp PNT) (TiPat PNT) 
   (TiPropDecorate.TiDecls PNT) -> (TiPat PNT, TiPropDecorate.TiExp PNT)
extPE k = case k of
       HsAlt _ p (HsBody e) _ -> (p,e)
       _ -> error ("HsHOLCF, transCases " ++ (show k)) 

extCL :: [TiPat PNT] -> [(String,Int)]
extCL ks = case ks of 
       [] -> [] -- error "Hs2HOLCF, extCL - case expression not allowed" 
       x:xs -> let p = (fst $ extCI x) 
           in if p /= [] then p else extCL xs
  
extCI :: (TiPat PNT) -> ([(String,Int)],String)
extCI k = case k of  -- ((cons, arity) list, cons). 
  TiPSpec (HsCon (PNT z (ConstrOf _ x) _)) _ _ -> 
     ([(gBN $ conName w, conArity w) | w <- constructors x], pp z)  
  TiPSpec (HsVar (PNT z _ _)) _ _ -> ([], pp z) 
  TiPApp m _ -> extCI m
  TiDecorate.Pat u -> case u of 
     HsPWildCard -> ([],"_")
     HsPParen p -> extCI p
     _ -> ([], pp u) 
  TiPTyped p _ ->  ([], pp p) 
  _ -> error ("H2HOLCF, extCI" ++ (show k)) 
 where 
  gBN (UniqueNames.PN q _) = q 
           
trCase :: Continuity -> (String,Int) -> 
       [((String,IsaPattern),IsaTerm)] 
                                 -> (IsaTerm,IsaTerm)
trCase r h ys = case ys of 
    [] -> case r of 
      IsCont -> (buildPat r h, IsaSign.Bottom)
      NotCont -> error "Hs2HOLCF, trCase: missing pattern"
    a:as -> if (fst $ fst a) == (fst h) 
       then (repVsCPt r (snd $ fst a) (snd a) (snd h))
       else if (fst $ fst a) == "_" 
       then (buildPat r h, snd a) 
       else trCase r h as 
 where
  repVsCPt r a b n = case a of
      IsaSign.Const _ _ -> (a,b)
      IsaSign.Paren x -> repVsCPt r x b n
      IsaSign.App x y z -> case y of 
        IsaSign.Free _ _ -> let 
             nv = (Free (mkVName $ "pX" ++ (show n)) noType)
             nr = renVars nv [y] b 
             st = repVsCPt r x nr (n-1) 
             nf = App (fst st) nv z
             ns = renVars nv [y] $ snd st 
           in (nf, ns)
      _ -> error "Hs2HOLCF, repVsCPt"  
  buildPat r (x,n) = 
     termMAppl r (Const (mkVName $ showIsaName x) noType) $ mkVVs n
  mkVVs n = if 0 < n 
     then (Free (mkVName $ "pX" ++ (show n)) noType):(mkVVs (n-1)) else []

transPatBind :: Continuity -> ConstTab -> PrDecl -> Maybe (IsaTerm,IsaTerm)
transPatBind a cs s = case s of
  TiPropDecorate.Dec (PropSyntaxStruct.Base 
        (HsDeclStruct.HsPatBind _ p (HsGuardsStruct.HsBody e) _)) -> do
              x <- transMPat a cs p
              y <- transMExp a cs e
              return (x, y) 
  _ -> error "HsHOLCF, transPatBind"

transMPat :: Continuity -> ConstTab -> PrPat -> Maybe IsaPattern
transMPat a cs t = case t of 
    TiDecorate.Pat p -> case p of
       HsPLit _ (HsInt n) -> return $ case a of
           IsCont -> 
              Const (mkVName $ "(Def (" ++ show n ++ "::int))") 
                     (IsaSign.Type "dInt" [] [])
           NotCont -> 
              Const (mkVName $ "(" ++ show n ++ "::int)") 
                     (IsaSign.Type "int" [] [])
       HsPList _ xs -> return $ case xs of 
          [] -> case a of
                  IsCont -> conDouble "lNil"
                  NotCont -> conDouble "[]"  
          _ -> error "Hs2HOLCF, transMPat, unsupported list notation" 
       _ -> transP a (mkVName . showIsaName) (transMPat a cs) p
    TiDecorate.TiPSpec w s _ -> case w of 
         HsVar x -> transHV a s x
         HsCon x -> transCN a s x
    TiDecorate.TiPTyped x _ -> transMPat a cs x
    TiDecorate.TiPApp w z -> do w1 <- transMPat a cs w 
                                z1 <- transMPat a cs z
                                return $ (termMAppl a w1 [z1])

transE :: Continuity -> 
     (PNT -> VName) -> (e -> Maybe IsaTerm) -> (p -> Maybe IsaPattern) -> 
            (EI PNT e p j h k) -> Maybe IsaTerm
transE c trId trE trP e =
 case (mapEI5 trId trE trP e) of 
   Just (HsId (HsVar _))              -> return $ conDouble "DIC"
   Just (HsApp x y)                   -> return $ termMAppl c x [y]  
   Just (HsLambda ps x)               -> return $ termMAbs c ps x 
   Just (HsIf x y z)                  -> return $ If x y z c 
   Just (HsTuple xs)                  -> return $ Tuplex xs c 
   Just (HsParen x)                   -> return $ Paren x
   _                                  -> Nothing -- Const "dummy" noType
--   _ -> error "Haskell2IsabelleHOLCF.transE, not supported"
--   HsId (HsCon c)              -> Const c noType
--   HsId (HsVar "==")              -> Const "Eq" noType     
--   HsLet ds e                  -> Let (map transPatBind ds) (transExp e) 
--   HsCase e ds                 -> Case e ds 
 
transP :: IsaName i => Continuity -> (i -> VName) -> (p -> Maybe IsaPattern) -> 
            (PI i p) -> Maybe IsaPattern
transP a trId trP p =
 case mapPI3 trId trP p of
   Just (HsPId (HsVar _))  -> return $ conDouble "DIC"
   Just (HsPTuple _ xs)    -> return $ Tuplex xs a 
   Just (HsPParen x)       -> return $ Paren x
   Just HsPWildCard        -> return $ Wildcard
   _                       -> Nothing 
--   HsPList ps -> plist ps
--   HsPId (HsCon c) -> Const c noType
--   HsPLit _ lit -> litPat (transL lit) -- new
--   HsPApp c ps -> App x y IsCont
--   HsPAsPat x p -> AsPattern (x,p)
--   HsPIrrPat p -> twiddlePat p

transCN :: Continuity -> HsScheme -> PNT -> Maybe IsaTerm
transCN c s x = let 
  y = showIsaName x
  z = transScheme c s 
  f w = Const (mkVName w) z
  in return $
  if elem pcpo (typeSort z) then case pp x of
      "True"   -> f "TT"
      "False"  -> f "FF"
      ":"      -> f "lCons"
      _        -> f y
  else case pp x of 
     "True"   -> f "True"
     "False"  -> f "False"      
     ":"      -> f "op #"
     _        -> f y

transHV :: Continuity -> HsScheme -> PNT -> Maybe IsaTerm
transHV a s x = let 
      n = showIsaName x 
      k = maybe noType id $ transMScheme a s
          --  maybe (error "Hs2HOLCF, transHV") id $ transMScheme a s
      tag = elem pcpo (typeSort k)
      qq = pp x
      mkConst w = Const (mkVName w) k
      mkVConst v = Const v k
      mkFree w = Free (mkVName w) k
      mFree w = Free (mkVName w) noType
      flist = [mFree "x", mFree "y"]
   in if qq == "error" then Nothing else return $
   case qq of  
   "==" -> mkConst "hEq"
   "/=" -> mkConst "hNEq"
--   "==" -> if tag == False then mkVConst "eqV"
--           else 
--     (termMAbs IsCont flist
--        (termLift $ termMAppl NotCont (mkVConst eqV)
--           flist))
   "&&" -> if tag == False then mkVConst conjV
            else mkConst "trand" 
   "||" -> if tag == False then mkVConst disjV
            else mkConst "tror"
   "+" -> (if tag == False then id
           else funFliftbin) $ mkVConst plusV
   "-" -> (if tag == False then id
           else funFliftbin) $ mkVConst minusV
   "*" -> (if tag == False then id
           else funFliftbin) $ mkVConst timesV
   "head" -> if tag == False then mkConst "hd"
              else mkConst "lHd"
   "tail" -> if tag == False then mkConst "tl"
              else mkConst "lTl" 
   ":"    -> if tag == False then mkVConst consV
              else mkConst "lCons" 
   "fst"    -> if tag == False then mkConst "fst"
              else mkConst "cfst" 
   "snd"    -> if tag == False then mkConst "snd"
              else mkConst "csnd" 
   ">>="    -> if tag == False then mkConst ">>="
              else mkConst "mBind" 
   ">>"     -> if tag == False then mkConst ">>"
              else mkConst "mSBind" 
   _ -> case x of
        PNT (PN _ (UniqueNames.G _ _ _)) _ _ -> mkConst n
        PNT (PN _ (UniqueNames.S _)) _ _ -> mkFree n
        PNT (PN _ (UniqueNames.Sn _ _)) _ _ -> mkFree n
        _ -> error "Haskell2IsabelleHOLCF, transHV"


---------------------------------- auxiliary --------------------------------

class IsaName i => TransFunction i j k where
 transFun :: (j i) -> k

mapEI5 :: (i1 -> i2) -> 
          (e1 -> Maybe e2) ->
          (p1 -> Maybe p2) ->
          EI i1 e1 p1 d t c ->
          Maybe (EI i2 e2 p2 d t c)
mapEI5 vf ef pf exp =
  case exp of
    HsId n                 -> return $ HsId (mapHsIdent2 vf vf n)
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
    HsList xs              -> do ys <- mapM ef xs
                                 return $ HsList ys
    _                      -> Nothing
--    HsLit s l              -> HsLit s l
--    HsCase e as          -> do f <- ef e
--                               bs <- map (mapA ef pf) as   
--                               return $ HsCase f bs 
--  where 
--    mapA f g k = case k of HsAlt _ p (HsBody e) _ -> 
       
--    HsLit s l              -> HsLit s l
--    HsInfixApp x op z      -> HsInfixApp (ef x) (mapHsIdent2 vf cf op) (ef z)
--    HsNegApp s x           -> HsNegApp s (ef x)  
--    HsLet ds e             -> HsLet (df ds) (ef e)
--    HsCase e alts          -> HsCase (ef e) (map (mapAlt ef pf df) alts) 
--    HsDo stmts             -> HsDo (mStmt stmts)
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

mapPI3 :: (i1 -> i2) ->
          (p1 -> Maybe p2) ->
          PI i1 p1 -> Maybe (PI i2 p2)
mapPI3 vf pf pat =
  case pat of
    HsPId n                -> return $ HsPId (mapHsIdent2 vf vf n)
    HsPLit s l             -> return $ HsPLit s l
    HsPTuple s ps          -> do bs <- mapM pf ps
                                 return $ HsPTuple s bs
    HsPParen p             -> do h <- pf p
                                 return $ HsPParen h 
    HsPWildCard            -> return $ HsPWildCard
    HsPList  s ps          -> do qs <- mapM pf ps
                                 return $ HsPList s qs
    HsPApp nm ps           -> do qs <- mapM pf ps
                                 return $ HsPApp (vf nm) qs
    HsPSucc s n l          -> return $ HsPSucc s (vf n) l
    _                      -> Nothing 
--    HsPNeg s l             -> HsPNeg s l
--    HsPNeg s l             -> HsPNeg s l
--    HsPSucc s n l          -> HsPSucc s (vf n) l
--    HsPInfixApp x op y     -> HsPInfixApp (pf x) (cf op) (pf y)
--    HsPApp nm ps           -> HsPApp (cf nm) (map pf ps)
--    HsPList  s ps          -> HsPList s (map pf ps)
--    HsPRec nm fields       -> HsPRec (cf nm) (mapFieldsI vf pf fields)
--    HsPAsPat nm p          -> HsPAsPat (vf nm) (pf p)
--    HsPIrrPat p            -> HsPIrrPat (pf p)


