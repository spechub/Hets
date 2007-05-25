{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  paolot@tzi.de
Stability   :  provisional
Portability :  non-portable (depends on programatica using MPTC)

theory translation for the embedding comorphism from Haskell to Isabelle.
-}

module Comorphisms.Hs2HOLCF (transTheory) where

import Monad

import qualified Data.Map as Map
import Common.Result
import Common.AS_Annotation
import Comorphisms.Hs2HOLCFaux

-- Haskell
import Haskell.HatAna as HatAna

-- Programatica
import NewPrettyPrint (pp)
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
import Isabelle.IsaConsts

------------------------------ Top level function -----------------------------
transTheory :: Continuity -> Bool -> HatAna.Sign -> [Named PrDecl]
            -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transTheory c m sign sens = do
  sign' <- transSignature c m sign
  (sign'',sens'') <- transSentencesI c sign' (map sentence sens)
  return (sign'', sens'')

------------------------------ Theory translation -----------------------------
{- Relevant theories in Programatica: base/Ti/TiClasses (for
tcTopDecls); property/parse2/Parse/PropPosSyntax (def of HsDecl).  -}

data ExpRole = FunDef | InstDef  -- no PLogic yet

data TSt a = TSt (ISign -> Result (a, ISign))

instance Monad TSt 
  where 
  return x = TSt (\w -> return (x,w))
  (TSt f) >>= g = TSt (\w -> do 
         (d,z) <- f w
         let (TSt q) = (g d) in q z)

transSentencesI :: Continuity -> ISign -> [PrDecl]
               -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transSentencesI c sign ls = let TSt f = transSentences c ls
   in do (a,b) <- f sign
         return (b, a)

transSentences :: Continuity -> [PrDecl]
               -> TSt [Named IsaSign.Sentence]
transSentences c ls = do
    xx0 <- mapM (transSentence c FunDef) ls
    xs  <- return [[s] | [s] <- xx0, extAxType s /= noType]
    yys <- insFixpoints c xs
    zz0 <- mapM (transSentence c InstDef) ls
    zz  <- return $ removeEL zz0
    zzs <- insFixpoints c zz 
    return (yys ++ zzs) 

transSentence :: Continuity -> ExpRole -> PrDecl
              -> TSt [Named IsaSign.Sentence]
transSentence c a (TiPropDecorate.Dec d) = case d of
  PropSyntaxStruct.Base p -> case (a,p) of
    (FunDef,  HsDeclStruct.HsFunBind _ ws) -> do
         k <- case ws of
                  [x] -> transMatch c x
                  _   -> transMMatch c ws
         return [k]
    (InstDef, HsInstDecl _ _ _ t (TiPropDecorate.Decs ds _)) -> 
         mapM (transIMatch c t)
                [y | TiPropDecorate.Dec (PropSyntaxStruct.Base
                               (HsDeclStruct.HsFunBind _ [y])) <- ds]
    _ -> return []
  _ -> return []

--------------------------- translation of sentences --------------------------
---------------------------- function definitions ---------------------------

transMatch :: Continuity  
           -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds
           -> TSt (Named Sentence)
transMatch c t = TSt $ \sign -> case (t, constTab sign) of
  (HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _, cs) ->
         let df = mkVName $ showIsaName nm
             tx = transExp c cs x
             y = maybe (noType) id $ Map.lookup df cs
             qs = map (transPat c cs) ps
         in return (makeSentence c (IsaSign.orig df) y df qs tx, sign)
  _ -> error "Hs2HOLCF.transMatch"

--------------------- inserts fixpoints ---------------------------------------

insFixpoints :: Continuity -> [[Named IsaSign.Sentence]] 
                -> TSt [Named IsaSign.Sentence]
insFixpoints c xs = TSt $ \ssg ->
              let ws = [[s] | s <- concat xs]
                  ys = fixMRec c ws
                  ac = newConstTab c ys
                  nc = Map.union (constTab ssg) ac
                  nssg = ssg {constTab = nc}
              in return (ys,nssg)

------------------------------- translates instances --------------------------

{- translates method definitions -}
transIMatch :: Continuity -> HsType
            -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds
            -> TSt (Named Sentence)
transIMatch a t s = TSt $ \sign -> case s of
   HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody ex) _ ->
         let ct = constTab sign
             nam = pp nm
             tx = if nam == "==" 
                  then equalExpression a 
                  else if nam == "/="
                  then nequalExpression a
                  else transExp a ct ex
             df = if nam == "==" then mkVName "hEq"
                  else if nam == "/=" then mkVName "hNEq"
                  else if nam == ">>=" then mkVName "mbind"
                  else mkVName $ showIsaName nm
             x =  transType a [] $ getInstType t      -- instatiating type
             w =  maybe [] id $ Map.lookup (typeId x) (arities $ tsig sign)
                                              -- all arities of inst. type
             c  = transClass $ getInstClass t       -- instantiated class
             cs = maybe [] id $ Map.lookup c (Map.fromList w)
                                   -- selects the arity for the inst. class
             xdf = IsaSign.orig df
             xx  = typeId x
             ndf = if elem nam ["return", ">>="] 
                   then xdf ++ "_" ++ xx
                   else xx ++ "_" ++ xdf
             pdf = if elem nam ["return", ">>="] 
                   then mkVName ndf else df
             nsg = if nam == "return" 
                   then addMonOpDecs sign xx -- x cs ndf  
                   else sign
             mty = if nam == "return" 
                   then returnType xx
                   else if nam == ">>="
                   then bindType xx
                   else if elem nam ["==","/="]
                   then equalType a x
                   else maybe (noType) id $ Map.lookup df ct 
                                                 -- abstract method type
             nty = repVarClass mty c (constrVarClass x cs)
             qs  = map (transPat a ct) ps
                     -- in ty, replaces the variable of class c with type x,
                     -- constraining variables in x with cs
             tst = makeSentence a ndf nty pdf qs tx
         in return (tst, nsg)
   _ -> error "Hs2HOLCF.transIMatch"

equalExpression :: Continuity -> Term
equalExpression a = let 
     vs = [varDouble "x", varDouble "y"]
     e = termMAppl NotCont (conDouble eq) vs
 in case a of 
   IsCont -> termMAbs IsCont vs (termAppl (conDouble "Def") e) 
   NotCont -> termMAbs NotCont vs e

nequalExpression :: Continuity -> Term
nequalExpression a = let 
     vs = [varDouble "x", varDouble "y"]
     e = termAppl (conDouble "~") (termMAppl NotCont (conDouble eq) vs)
 in case a of 
     IsCont -> termMAbs IsCont vs (termAppl (conDouble "Def") e )
     NotCont -> termMAbs NotCont vs e

equalType :: Continuity -> IsaType -> IsaType
equalType a t = case a of 
   NotCont -> mkFunType t $ mkFunType t boolType
   IsCont  -> mkContFun t $ mkContFun t $ IsaSign.Type "tr" dom []

returnType :: String -> IsaType
returnType t = let 
    v = TFree "a" holType
    x = IsaSign.Type t holType [v] 
 in IsaSign.Type "=>" holType [v,x]

bindType :: String -> IsaType
bindType t = let 
    va = TFree "a" holType
    vb = TFree "b" holType
    xa = IsaSign.Type t holType [va]
    xb = IsaSign.Type t holType [vb]
    f  = IsaSign.Type "=>" holType [va, xb]
    g  = IsaSign.Type "=>" holType [f, xb] 
 in IsaSign.Type "=>" holType [xa, g]

addMonOpDecs :: ISign -> String -> ISign
addMonOpDecs sign xx = let
             nrt = returnType xx  
             nbd = bindType xx  
             jrt = mkVName $ "return_" ++ xx
             jbd = mkVName $ "mbind_" ++ xx  
             qqs = Map.fromList [(jrt, nrt), (jbd, nbd)]
             nc = Map.union (constTab sign) qqs
          in sign {constTab = nc}             

extHead :: IsaType -> IsaType
extHead t = case t of 
   IsaSign.Type "=>" _ [_,b] -> extHead b
   _ -> t

------------------------ translate pattern matching definitions ---------------

-- Main function. transMultiDef translate the expressions,
-- formCaseExp builds the case expression.
transMMatch :: Continuity 
            -> [HsDeclStruct.HsMatchI PNT PrExp PrPat ds]
            -> TSt (Named Sentence)
transMMatch c ds = TSt $ \sign -> case ds of
   [] -> error "Hs2HOLCF.transMMatch"
   a : _ -> let
      (a1, a2) = extInfo a
      cs = constTab sign
      df = mkVName $ showIsaName a1
      ls = map (snd . extInfo) ds
      ww = transMultiDef c cs ls
      tx = formCaseExp c ww
      y  = maybe (noType) id $ Map.lookup df cs
      qs = map (mkVs "qX" . snd) $ zip (fst a2) [(1 :: Int)..]
    in return (makeSentence c (IsaSign.orig df) y df qs tx, sign)
 where
   extInfo m = case m of
       HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _ ->
           (nm, (ps, x))
       _ -> error "Hs2HOLCF.extInfo"

makeSentence :: Continuity -> String -> IsaType -> VName -> [IsaPattern]
             -> IsaTerm -> Named Sentence
makeSentence a d y df ps tx =
  makeNamed d $ ConstDef $ if tx == xDummy
  then IsaEq xDummy $ xDummy
  else IsaEq (Const df y) $ termMAbs a ps tx

----------------------------------------------------------------------------
-- annotated translation function. To each parameter pattern - IsaPattern -
-- is associated
-- datatype information - [(String,Int)]
-- case variable name - IsaTerm
-- parameter name before translation - String
transMultiDef :: Continuity -> ConstTab -> [([PrPat], PrExp)]
    -> [([([(String, Int)],((IsaTerm, String), IsaPattern))], IsaTerm)]
transMultiDef c sign ls =
  let
   ws = csAris [fst w | w <- ls]
   ks = [([newInfo v | v <- xs], transExp c sign y) | (xs, y) <- ls]
   ss = map standizeVars ks
 in [(zipNE ws rs, s) | (rs,s) <- ss]
 where
  newInfo f = (snd $ extCI f, transPat c sign f)
  zipNE ws rs = case ws of
    [] -> []
    hd : xs -> (case hd of
           [] -> []
           _ -> [(hd, head rs)]) ++ zipNE xs (tail rs)

-- Extract datatype information from a list of patterned parameter lists.
-- Returns the list of constructors and arities for the parameter datatypes.
csAris :: [[PrPat]] -> [[(String,Int)]]
csAris ls = case ls of
 [] -> error "Hs2HOLCF.csAris"
 m : _ -> case m of
  [] -> []
  _ : _ -> extCL (map head ls) : csAris [tail a | a <- ls]

-- Standardizes parameter names from all the expressions.
-- Associates a case variable name.
standizeVars :: ([(String, IsaPattern)], IsaTerm)
             -> ([((IsaTerm, String), IsaPattern)], IsaTerm)
standizeVars k' = let
   mkqXVs = mkVs "qX"
   stdVars (cs, sd) i = case cs of
    [] -> ([], sd)
    (a, b) : as -> let
       na = sbVs (b, i)
       nk = renVars na [b] sd
       (ls, y) = stdVars (as, nk) (i + 1)
     in (((mkqXVs i, a), na) : ls, y)
   sbVs a = case a of
    (Free _, b) -> mkqXVs b
    (f, _) -> f
 in stdVars k' 1

mkVs :: String -> Int -> IsaTerm
mkVs str n = Free (mkVName $ str ++ show n)

-- Forms the nested case expression, using trCase.
formCaseExp :: Continuity ->
       [([([(String,Int)],((IsaTerm,String),IsaPattern))],IsaTerm)]
              -> IsaTerm
formCaseExp ct ls =
 case ls of
 [] -> error "Hs2HOLCF.formCaseExp"
 m : _ -> case fst m of
   [] -> snd m
   h : _ -> let
      k1s = map fst ls
      xs = map head k1s
      xxs = remove_duplicates [((snd $ fst $ snd x, snd $ snd x),
                [(us,t) | (u:us,t) <- ls, u == x] ++
                     [(us,t) | ((_,(_,Free _)):us,t) <- ls]) | x <- xs]
      ws = remove_duplicates $ [((a,b),formCaseExp ct c) | ((a,b),c) <- xxs]
    in makeCase (fst $ fst $ snd h) $ map (\z -> trCase ct z ws) (fst h)
 where
  makeCase t lst = Case t lst

------------------------------ Signature translation --------------------------

transSignature :: Continuity -> Bool -> HatAna.Sign -> Result IsaSign.Sign
transSignature c m sign =  let
 tys  = HatAna.types sign
 vals = HatAna.values sign
 xx   = getDomainTab c vals
 in Result [] $ Just $ IsaSign.emptySign
  { baseSig = case (c,m) of
                   (IsCont,False) -> HsHOLCF_thy
                   (NotCont,False) -> HsHOL_thy
                   (IsCont,True) -> MHsHOLCF_thy
                   (NotCont,True) -> MHsHOL_thy,
    tsig = emptyTypeSig
           {
             classrel = getClassrel c tys,
             abbrs = getAbbrs c tys,
             arities = getArities c xx (HatAna.instances sign)
           },
    constTab =  getConstTab c vals,
    domainTab = xx
  }

------------------------------ translation of types ---------------------------
{- This signature translation takes after the one to Stratego, and relies on
 Isabelle.Translation to solve naming conflicts. -}

transType :: Continuity -> [HsType] -> HsType -> IsaType
transType a c t = maybe noType id $ transMType a c t

transMType :: Continuity -> [HsType] -> HsType -> Maybe IsaType
transMType a c (Typ t) = transT a
        (transIdV a c) (transIdC a) (transMType a c) t

transT :: Continuity -> (PNT -> Maybe IsaType)
       -> (PNT -> Maybe IsaType) -> (d -> Maybe IsaType)
       -> TI PNT d -> Maybe IsaType
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

mapTI3 :: (i1 -> Maybe i2) -> (i1 -> Maybe i2) -> (t1 -> Maybe t2)
       -> TI i1 t1 -> Maybe (TI i2 t2)
mapTI3 vf cf tf hty = case hty of
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

------------------------------ Class translation ------------------------------

transClass :: HsType -> IsaClass
transClass x = case x of
    Typ (HsTyCon c) -> IsaClass (showIsaName c)
    Typ _ -> error "Hs2HOLCF.transClass"
-- need check of parameters?

------------------------------- no Kind translation ---------------------------

------------------------------- SIGN fields translation -----------------------
------------------------------- translation for ConstTab ----------------------

getConstTab ::  Continuity -> VaMap -> ConstTab
getConstTab c = Map.map fst . Map.filter ((== IsaVal) . snd) . getAConstTab c

getAConstTab ::  Continuity -> VaMap -> AConstTab
getAConstTab c f =
    liftMapByListD Map.toList Map.fromList (mkVName . showIsaName . fst)
         (\ (x, y) -> (transMScheme c y, getValInfo x)) nothingFiOut f

getValInfo :: HsId -> IsaVT
getValInfo n = case n of
   HsCon _ -> IsaConst
   _ -> IsaVal

transMScheme :: Continuity -> HsScheme -> Maybe IsaType
transMScheme a s = case s of
    Forall _ _ (c TiTypes.:=> t) -> transMType a c t

------------------------------ translation of domaintab -----------------------

getDomainTab :: Continuity -> VaMap -> DomainTab
getDomainTab c f =  let
  ls = remove_duplicates
     [getDomainEntry (getAConstTab c f) x | x <- Map.keys f, checkTyCons x]
  in reverse $ getDepDoms ls

getDomainEntry :: AConstTab -> HsId -> [DomainEntry]
getDomainEntry ctab t = case t of
  HsCon (PNT _ (TypedIds.ConstrOf _ d) _) ->
     [(getDomType ctab (mkVName $ showIsaName t), [(b, getFieldTypes ctab b)
         | b <- [ mkVName $ showIsaName c
                   | PN c _ <-  map conName (constructors d)]])]
  _ -> []

----------------------------- translation for Classrel (from KEnv) ------------

getClassrel :: Continuity -> TyMap -> Classrel
getClassrel c f = liftMapByList Map.toList Map.fromList
                  (IsaClass . showIsaName) (transClassInfo c) f

transClassInfo :: Continuity -> (Kind, HsTypeInfo) -> Maybe [IsaClass]
transClassInfo c p = case snd p of
  TiTypes.Class _ _ _ _ ->
    Just $ remove_duplicates $ (case c of
                       IsCont -> dom
                       NotCont -> holType)
             ++ map transClass (extClassInfo $ snd p)
  _ -> Nothing

------------------------- translation of Abbrs (from KEnv) --------------------

getAbbrs ::  Continuity -> TyMap -> Abbrs
getAbbrs c = Map.foldWithKey (\ k v -> case v of
           Nothing -> id
           Just p -> Map.insert k p) Map.empty
        . liftMapByList Map.toList Map.fromList showIsaName (transAbbrsInfo c)

transAbbrsInfo :: Continuity -> (Kind, HsTypeInfo) -> Maybe ([TName], IsaType)
transAbbrsInfo c p = case (snd p) of
  TiTypes.Synonym _ _ -> let (x, y) = extAbbrsInfo (snd p) in
      Just (map showIsaName x, transType c [] y)
  _ -> Nothing

---------------------------- translation of arities ---------------------------

getArities :: Continuity -> DomainTab -> HsInstances -> IsaSign.Arities
getArities c dt db = Map.fromList (groupInst $ getTypeInsts c dt db)

getTypeInsts :: Continuity -> DomainTab -> HsInstances -> [IsaTypeInsts]
getTypeInsts c dt db =
    [(typeId $ transType c [] $ getMainInstType x, [transInst c x]) | x <- db]
    ++ [(u,[(IsaClass "Eq", [])]) | [(IsaSign.Type u _ [],_)] <- dt]

transInst :: Continuity -> HsInstance -> (IsaClass, [(IsaType, [IsaClass])])
transInst c i = let (x, y) = prepInst i
                    w = case c of
                         IsCont -> pcpo
                         NotCont -> isaTerm
  in (transClass x,
      reverse [(transType c [] a, w : map transClass b) | (a, b) <- y])


--------------------------------- Term translation ----------------------------
-------------------------------------------- term and patterns ----------------

transExp :: Continuity -> ConstTab -> PrExp -> IsaTerm
transExp a c t = maybe xDummy id $ transMExp a c t

transPat :: Continuity -> ConstTab -> PrPat -> IsaPattern
transPat a c t = maybe xDummy id $ transMPat a c t

liftExp :: Continuity -> String -> Typ -> IsaTerm
liftExp c n t = case c of
  IsCont -> App (conDouble "Def") 
             (Const (mkVName n) t) NotCont 
                        -- (IsaSign.Type "!!!" [] [t])) NotCont
  NotCont -> Const (mkVName n) t 
                        -- (IsaSign.Type "!!!" [] [t])

transMExp :: Continuity -> ConstTab -> PrExp -> Maybe IsaTerm
transMExp a cs t = let
   tInt = IsaSign.Type "int" holType []
   tRat = IsaSign.Type "Rat" holType []
  in case t of
    (TiPropDecorate.Exp e) -> case e of
       HsLit _ (HsInt n) -> return $ liftExp a (show n) tInt
       HsLit _ (HsFloatPrim n) -> return $ liftExp a (show n) tRat
       HsList xs -> return $ case xs of
          [] -> case a of
                   IsCont -> conDouble "nil"
                   NotCont -> conDouble "[]"
          _ -> error "Hs2HOLCF.transMExp" -- unsupported list notation
       HsLet (TiPropDecorate.Decs ds _) k -> do
          w <- mapM (transPatBind a cs) ds
          z <- transMExp a cs k
          return $ Let w z
       HsCase e' as -> do
          e1 <- transMExp a cs e'
          bs <- transCases a cs (map extPE as)
          return $ Case e1 bs
       _ -> transE a (mkVName . showIsaName) (transMExp a cs)
                                     (transMPat a cs) e
    TiPropDecorate.TiSpec w _ bb -> case w of
       HsVar x -> transHV a x bb
       HsCon x -> transCN a x 
    TiPropDecorate.TiTyped x _ -> transMExp a cs x

transCases :: Continuity -> ConstTab -> [(TiPat PNT, TiPropDecorate.TiExp PNT)]
           -> Maybe [(IsaTerm,IsaTerm)]
transCases r cs ks = case ks of
 [] -> return []
 _ : _ -> let
     cnn = extCL $ map fst ks -- (cons, arity) list for the case value.
     ys = [((snd $ extCI f, transPat r cs f), transExp r cs g)
                             | (f,g) <- ks] -- (cons, (ptn, exp)) list.
  in if null cnn then error "Hs2HOLCF.transCases"
       else return $ map (\h -> trCase r h ys) cnn

extPE :: HsGuardsStruct.HsAlt (TiPropDecorate.TiExp PNT) (TiPat PNT)
   (TiPropDecorate.TiDecls PNT) -> (TiPat PNT, TiPropDecorate.TiExp PNT)
extPE k = case k of
       HsAlt _ p (HsBody e) _ -> (p,e)
       _ -> error "HsHOLCF.extPE"

extCL :: [TiPat PNT] -> [(String,Int)]
extCL ks = case ks of -- ((cons, arity) list, cons).
       [] -> []
       x:xs -> let p = (fst $ extCI x)
           in if p /= [] then p else extCL xs

extCI :: (TiPat PNT) -> ([(String,Int)],String)
extCI k = case k of
  TiPSpec (HsCon (PNT z (ConstrOf _ x) _)) _ _ ->
     ([(gBN $ conName w, conArity w) | w <- constructors x], pp z)
  TiPSpec (HsVar (PNT z _ _)) _ _ -> ([], pp z)
  TiPApp m _ -> extCI m
  TiDecorate.Pat u -> case u of
     HsPWildCard -> ([],"_")
     HsPParen p -> extCI p
     _ -> ([], pp u)
  TiPTyped p _ ->  ([], pp p)
  _ -> error "H2HOLCF.extCI"
 where
  gBN (UniqueNames.PN q _) = q

trCase :: Continuity -> (String, Int) -> [((String, IsaPattern), IsaTerm)]
       -> (IsaTerm, IsaTerm)
trCase r h ys = case ys of
    [] -> case r of
      IsCont -> (buildPat r h, conDouble "UU")
      NotCont -> error "Hs2HOLCF.trCase"
    ((a, b), c) : as -> if a == fst h
       then repVsCPt b c (snd h)
       else if a == "_"
       then (buildPat r h, c)
       else trCase r h as
 where
  mkpXVs = mkVs "pX"
  repVsCPt a b n = case a of
      IsaSign.Const _ _ -> (a, b)
      IsaSign.App x y@(IsaSign.Free _) z -> let
             nv = mkpXVs n
             nr = renVars nv [y] b
             st = repVsCPt x nr (n-1)
             nf = App (fst st) nv z
             ns = renVars nv [y] $ snd st
           in (nf, ns)
      _ -> error "Hs2HOLCF.repVsCPt"
  buildPat r' (x, n) = let
     hh = stringTrans r' Nothing x
     k = Const (mkVName $ showIsaName x) noType
     j = maybe k id hh
   in termMAppl r' j $ reverse $ map mkpXVs [1..n]

transPatBind :: Continuity -> ConstTab -> PrDecl -> Maybe (IsaTerm,IsaTerm)
transPatBind a cs s = case s of
  TiPropDecorate.Dec (PropSyntaxStruct.Base
        (HsDeclStruct.HsPatBind _ p (HsGuardsStruct.HsBody e) _)) -> do
              x <- transMPat a cs p
              y <- transMExp a cs e
              return (x, y)
  _ -> error "HsHOLCF.transPatBind"

transMPat :: Continuity -> ConstTab -> PrPat -> Maybe IsaPattern
transMPat a cs t = let
   tInt = IsaSign.Type "int" holType []
  in case t of
    TiDecorate.Pat p -> case p of
       HsPLit _ (HsInt n) -> return $ liftExp a (show n) tInt
       HsPList _ xs -> return $ case xs of
          [] -> case a of
                  IsCont -> conDouble "nil"
                  NotCont -> conDouble "[]"
          _ -> error "Hs2HOLCF.transMPat" -- unsupported list notation
       _ -> transP a (mkVName . showIsaName) (transMPat a cs) p
    TiDecorate.TiPSpec w _ bb -> case w of
         HsVar x -> transHV a x bb
         HsCon x -> transCN a x
    TiDecorate.TiPTyped x _ -> transMPat a cs x
    TiDecorate.TiPApp w z -> do w1 <- transMPat a cs w
                                z1 <- transMPat a cs z
                                return $ (termMAppl a w1 [z1])

transE :: Continuity -> (PNT -> VName) -> (e -> Maybe IsaTerm)
       -> (p -> Maybe IsaPattern) -> (EI PNT e p j h k) -> Maybe IsaTerm
transE c trId trE trP e =
 case (mapEI5 trId trE trP e) of
   Just (HsId (HsVar _))              -> return $ conDouble "DIC"
   Just (HsApp x y)                   -> return $ termMAppl c x [y]
   Just (HsLambda ps x)               -> return $ termMAbs c ps x
   Just (HsIf x y z)                  -> return $ If x y z c
   Just (HsTuple xs)                  -> return $ Tuplex xs c
   Just (HsParen x)                   -> return x
   _                                  -> Nothing

transP :: IsaName i => Continuity -> (i -> VName) -> (p -> Maybe IsaPattern)
       -> (PI i p) -> Maybe IsaPattern
transP a trId trP p =
 case mapPI3 trId trP p of
   Just (HsPId (HsVar _))  -> return $ conDouble "DIC"
   Just (HsPTuple _ xs)    -> return $ Tuplex xs a
   Just (HsPParen x)       -> return x
   Just HsPWildCard        -> return $ Free $ mkVName "_"
   _                       -> Nothing

transCN :: Continuity -> PNT -> Maybe IsaTerm
transCN c x = let
    k = pp x
    y = showIsaName x
    w = Const (mkVName y) noType
    zz = stringTrans c Nothing k
  in return $ maybe w id $ zz

transHV :: Continuity -> PNT -> [HsType] -> Maybe IsaTerm
transHV a x tt = let
      n = showIsaName x
      qq = pp x
      mkConst w = Const (mkVName w) noType
      mkFree w = Free (mkVName w)
   in if qq == "error" then Nothing else return $
   case (stringTrans a (Just tt) qq) of
   Just d -> d
   Nothing -> case x of
        PNT (PN _ (UniqueNames.G _ _ _)) _ _ -> mkConst n
        PNT (PN _ (UniqueNames.S _)) _ _ -> mkFree n
        PNT (PN _ (UniqueNames.Sn _ _)) _ _ -> mkFree n
        _ -> error "Hs2HOLCF.transHV"

stringTrans :: Continuity -> Maybe [HsType] -> String -> Maybe IsaTerm
stringTrans a t qq = let
      mkConst w = Const (mkVName w) noType
      mkVConst v = Const v noType
   in if qq == "error" then Nothing else
   case qq of
   "==" -> return $ mkConst "hEq"
   "/=" -> return $ mkConst "hNEq"
   "&&" -> return $ if a == NotCont then mkVConst conjV
            else mkConst "trand"
   "||" -> return $ if a == NotCont then mkVConst disjV
            else mkConst "tror"
   "+" -> return $ (if a == NotCont then id
           else funFliftbin) $ mkVConst plusV
   "-" -> return $ (if a == NotCont then id
           else funFliftbin) $ mkVConst minusV
   "*" -> return $ (if a == NotCont then id
           else funFliftbin) $ mkVConst timesV
   "head"  -> return $ if a == NotCont then mkConst "hd"
              else mkConst "HD"
   "tail"  -> return $ if a == NotCont then mkConst "tl"
              else mkConst "TL"
   ":"     -> return $ if a == NotCont then mkVConst consV
              else mkConst "op ##"
   "[]"    -> return $ if a == NotCont then mkConst "[]"
              else mkConst "nil"
   "fst"   -> return $ if a == NotCont then mkConst "fst"
              else mkConst "cfst"
   "snd"   -> return $ if a == NotCont then mkConst "snd"
              else mkConst "csnd"
   "return" -> return $ mkTyConst a t "return" 
   ">>="   -> return $ mkTyConst a t "mbind"
   ">>"    -> return $ mkTyConst a t ">>"
   "True"  -> return $ if a == NotCont then mkConst "True"
              else mkConst "TT"
   "False" -> return $ if a == NotCont then mkConst "False"
              else mkConst "FF"
   "Just"  -> return $ mkConst $ if a == NotCont then "Some" 
              else "return"
   "Nothing" -> return $ mkConst $ if a == NotCont then "None"
                else "fail"
   _       -> Nothing
   where 
   mkTyConst aa tt s = let 
                     kt = case tt of 
                          Just (x:_) -> transType aa [] x
                          _ -> noType
                     w = typeId $ extHead kt
                     ndf = s ++ "_" ++ w                  
                 in  Const (mkVName ndf) noType 


---------------------------------- auxiliary --------------------------------

mapEI5 :: (i1 -> i2) -> (e1 -> Maybe e2) -> (p1 -> Maybe p2)
       -> EI i1 e1 p1 d t c -> Maybe (EI i2 e2 p2 d t c)
mapEI5 vf ef pf ex =
  case ex of
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

mapPI3 :: (i1 -> i2) -> (p1 -> Maybe p2) -> PI i1 p1 -> Maybe (PI i2 p2)
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

