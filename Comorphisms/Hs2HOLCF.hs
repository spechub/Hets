{- |
Module      :  $Header: /repository/HetCATS/Comorphisms/Hs2HOLCF.hs,v 1.42 2007/05/25 10:49:58 paolot Exp $
Description :  theory translation for the embedding comorphism from Haskell to Isabelle
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  paolot@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (depends on programatica using MPTC)

theory translation for the embedding comorphism from Haskell to Isabelle.
-}

module Comorphisms.Hs2HOLCF (transTheory) where

import qualified Data.Map as Map

import Common.Utils (number)
import Common.Result
import Common.AS_Annotation

import Comorphisms.Hs2HOLCFaux

-- Haskell
import Haskell.HatAna as HatAna

-- Programatica
import NewPrettyPrint (pp)
import TypedIds

import TiTypes

import PNT
import UniqueNames

import TiPropDecorate
import PropSyntaxStruct
import HsDeclStruct
import HsGuardsStruct
import TiDecorate

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts

import Debug.Trace

------------------------------ Top level function ------------------------

transTheory :: Continuity -> Bool -> HatAna.Sign -> [Named PrDecl]
            -> Result (IsaSign.Sign, [Named IsaSign.Sentence])
transTheory c m sign sens = do
  sign' <- transSignature c m sign
  (sign'',sens'') <- transSentencesI c sign' (map sentence sens)
  return (sign'', concatMap (\ (t, l) ->
         map (\ (r, ars) -> makeNamed ""
              $ Instance t (map snd ars) [r] [] $ toIsaProof DotDot) l)
         (filter (not . flip elem
                   ["unitT", "intT", "integerT", "charT", "ratT"] . fst)
          $ Map.toList $ arities $ tsig sign'') ++ sens'')

------------------------------ Theory translation ------------------------
{- Relevant theories in Programatica: base/Ti/TiClasses (for
tcTopDecls); property/parse2/Parse/PropPosSyntax (def of HsDecl)  -}

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
         return (ff b, a)
   where ff x = x {constTab = Map.filter (/= noTypeT) $ constTab x}

-------------------------------------------------------------------

transSentences :: Continuity -> [PrDecl]
               -> TSt [Named IsaSign.Sentence]
transSentences c ls = do
    xx0  <- mapM (transSentence c FunDef) ls
    xs   <- return [[s] | [s] <- xx0, notDummy s]
    yys  <- insFixpoints c xs
    zz0  <- mapM (transSentence c InstDef) ls
    zz1  <- return $ removeEL zz0
    zz2  <- insFixpoints c zz1
    zz3  <- return $ filter notDummy (yys ++ zz2)
    zz   <- return $ filter (\x -> extAxType x /= noTypeT) zz3
    return zz

notDummy  ::   Named Sentence -> Bool
notDummy s = case sentence s of
  ConstDef (IsaEq t _)     ->
          if t /= xDummy then True else False
  RecDef _ []              -> False
  RecDef _ [[]]              -> False
  RecDef _ ((IsaEq t _ : _) : _) ->
          if t /= xDummy then True else False
  _  -> True

transSentence :: Continuity -> ExpRole -> PrDecl
              -> TSt [Named IsaSign.Sentence]
transSentence c a (TiPropDecorate.Dec d) =
 case d of
   PropSyntaxStruct.Base p -> case (a,p) of
      (FunDef,  HsDeclStruct.HsFunBind _ ws) -> do
           k <- case ws of
                  _   -> transMMatch c ws
           return [k]
      (FunDef,  HsPatBind _ q (HsBody e) _) -> do
           k <- transCProp FunDef c q e
           return [k]
      (InstDef, HsInstDecl _ _ _ t (TiPropDecorate.Decs ds _)) -> do
           k <- mapM (transIMatch c t)
                [y | TiPropDecorate.Dec (PropSyntaxStruct.Base
                               (HsDeclStruct.HsFunBind _ [y])) <- ds]
           w <-
              mapM (uncurry $ transCProp InstDef c) [(q,e) |
                 TiPropDecorate.Dec (PropSyntaxStruct.Base
                    (HsDeclStruct.HsPatBind _ q (HsBody e) _)) <- ds]
           return (k ++ w)
      _ -> return []
   _ -> return []

-------------- main functions for sentence translation -------------------
--------------------- inserts fixpoints ----------------------------------

insFixpoints :: Continuity -> [[Named IsaSign.Sentence]]
                -> TSt [Named IsaSign.Sentence]
insFixpoints c xs = TSt $ \ssg ->
              let ws = [[s] | s <- concat xs]
                  ys = fixMRec c ws
                  ac = newConstTab c ys
                  nc = Map.union (constTab ssg) ac
                  nssg = ssg {constTab = nc}
              in return (ys,nssg)

--------------------------- constants -----------------------------------

constTabM :: TSt ConstTab
constTabM = TSt $ \sign -> return (constTab sign, sign)

transCProp :: ExpRole -> Continuity
            -> PrPat -> PrExp
            -> TSt (Named Sentence)
transCProp j a p e = do
   cs <- constTabM
   case (transPatBindX True a cs p e) of
      Just (x,y) -> let k = fst $ extTBody x
        in case (getTermName k) of
          Nothing    -> trace (show p) $ error "Hs2HOLCF.transCProp1"
          Just nm    -> case j of
            InstDef -> case p of
              TiPSpec (HsVar r) _ _ -> case (extClass r) of
                 Just c -> case e of
                     (TiPropDecorate.Exp (HsApp
                          (TiPropDecorate.TiSpec _ _ (g:_)) _)) ->
                              transInstEx a nm (mkVName nm)
                                   (IsaClass c) (transType a [] g)
                                      (typ $ termType x) [] y
                     _  -> trace (show p) $ error "Hs2HOLCF.transCProp2"
                 _      -> trace ("\n ER000: " ++ show j) $
                           trace ("\n ER111: " ++ show p) $
                           trace ("\n ER222: " ++ show e) $
                                     error "Hs2HOLCF.transCProp3"
              _     -> error "Hs2HOLCF.transCProp4"
            FunDef  -> return $ makeNamed nm $ ConstDef $ IsaEq x y
      _          -> trace ("\n PAT: " ++ show p) $
                    trace ("\n EXP: " ++ show e) $
                    error "Hs2HOLCF.transCProp5"

------------------ translate pattern matching definitions ---------------
-- Main function. transMultiDef translate the expressions,
-- formCaseExp builds the case expression.
transMMatch :: Show ds => Continuity
            -> [HsDeclStruct.HsMatchI PNT PrExp PrPat ds]
            -> TSt (Named Sentence)
transMMatch c ds = TSt $ \sign -> case ds of
   []   -> error "Hs2HOLCF.transMMatch"
   a:_  -> let
            cs = constTab sign
            (a1, a2) = extInfo c cs a
            df = mkVName $ showIsaName a1
            y  = maybe (noTypeT) id $ Map.lookup df cs
            ls = map (snd . extInfo c cs) ds
        in case ls of
            []        -> error ("Hs2HOLCF.transMMatch 2")
            [(ps,tx)] -> let
                 qs = wrapWild $ map (transPat c cs) ps
              in mkkSent c df y qs tx sign
            _         -> let
                 ww = transMultiDef c cs ls
                 tx = formCaseExp c ww
                 qs = map (mkVs "qX" . snd) $
                            zip (fst a2) [(1 :: Int)..]
              in mkkSent c df y qs tx sign
 where
   extInfo c' cs' m = case m of
     HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody x) _   ->
           (nm, (elimDic ps, transExp c' cs' x))
     HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsGuard xs) _ ->
        let ys = [(transExp c' cs' x1, transExp c' cs' x2)
                                            | (_,x1,x2) <- xs]
            k = buildIfs c' ys
            ps' = elimDic ps
        in (nm, (ps', k))
   mkkSent c' df' y' qs' tx' sign' = return
       (makeSentence FunDef c' (IsaSign.orig df') y' df' qs' tx', sign')
   wrapWild ls = map wrapW $ number ls
   wrapW (a,n) = case a of
        Free x -> case new x of
            "wildcX" -> Free $ mkVName ("wildcX" ++ show n)
            _ -> a
        _ -> a

elimDic :: [PrPat] -> [PrPat]
elimDic ls = case ls of
   [] -> []
   x : xs -> let r = elimDic xs in case x of
      TiDecorate.Pat (HsPId (HsVar _)) -> r
      _ -> x : r

------------------------- translates instances --------------------------
{- translates method definitions -}
transIMatch :: (Show ds) => Continuity -> HsType
            -> HsDeclStruct.HsMatchI PNT PrExp PrPat ds
            -> TSt (Named Sentence)
transIMatch a t s = do
  ct <- constTabM
  case s of
     HsDeclStruct.HsMatch _ nm ps (HsGuardsStruct.HsBody ex) _ ->
         let nam =  showIsaName nm
             df  = mkVName $ showIsaName nm
             tx  = transExp a ct ex
             qs  = map (transPat a ct) ps
             gt  = getInstType t      -- instatiating type
             x   = transType a [] $ gt      -- instatiating type
             c   = transClass $ getInstClass t
                                            -- instantiated class
         in transInstEx a nam df c x noTypeT qs tx
     _  -> error "Hs2HOLCF, transIMatch"

transInstEx :: Continuity -> String -> VName ->
      IsaClass -> IsaType -> IsaType ->
        [IsaTerm] -> IsaTerm -> TSt (Named Sentence)
transInstEx a nam df c@(IsaClass k) x x2 qs tx = TSt $ \sign ->
         let ct  = constTab sign
             xx  = typeId x
             w   = maybe [] id $ Map.lookup xx (arities $ tsig sign)
                                           -- all arities of inst. type
             cs  = maybe [] id $ Map.lookup c (Map.fromList w)
                               -- selects the arity for the inst. class
             xdf = new df
             ndf = if enElem nam aweLits
                   then xdf ++ "_" ++ xx
                   else xx ++ "_" ++ xdf
             pdf = if enElem nam aweLits
                   then mkVName ndf else df
             nsg = if enElem nam ["return"]
                   then addMonOpDecs sign xx
                   else sign
             mty = if enElem nam ["return"]
                   then returnType xx
                   else if enElem nam [">>="]
                   then bindType xx
                   else if enElem nam ["fail",">>"]
                   then noTypeT
                   else if enElem nam mthAll
                   then mthTy a k nam
                   else maybe x2 id $ Map.lookup df ct
                                             -- abstract method type
             nty = instTyp mty c x cs
                 -- in mty, replaces the variable of class c with type x,
                 -- constraining variables in x with cs
             ntx = if enElem nam mthEq
                   then (case tx of
                              IsaSign.Const bb _ ->
                                 if new bb == (xdf ++ "DF")
                                 then defaultDef a nam x c cs
                                 else tx
                              _  -> tx)
                   else tx
             tst = makeSentence InstDef a ndf nty pdf qs ntx
         in return (tst, nsg)

instTyp :: IsaType -> IsaClass -> IsaType -> [(IsaType,Sort)] -> IsaType
instTyp t c x cs = repVarClass t c (constrVarClass x cs)

defaultDef :: Continuity -> String -> IsaType -> IsaClass ->
                         [(IsaType,Sort)] -> IsaTerm
defaultDef c x t k@(IsaClass r) ks = let
      w = mthTy c r x
      z = instTyp w k t ks
   in if enElem x ["=="] then eqDef c z
      else if enElem x ["/="] then neqDef c z
      else error "HsHOLCFaux, defaultDef"

eqDef :: Continuity -> IsaType -> IsaTerm
eqDef c t = let vs = [mkFree "x", mkFree "y"]
  in termMAbs c vs $ termMAppl c (notPT c) $ [termMAppl c (neqTPT t) vs]

neqDef :: Continuity -> IsaType -> IsaTerm
neqDef c t = let vs = [mkFree "x", mkFree "y"]
  in termMAbs c vs $ termMAppl c (notPT c) $ [termMAppl c (eqTPT t) vs]

-------------------- theory trans auxiliaries ------------------------
-------------------- transMMatch auxs -------------------------------

buildIfs :: Continuity -> [(IsaTerm,IsaTerm)] -> IsaTerm
buildIfs c xs = case xs of
  []  -> bottomPT c
  (y1,y2):ys -> case (getTermName y1) of
        Just "otherwise" -> y2
        _                -> If y1 y2 (buildIfs c ys) c

makeSentence :: ExpRole -> Continuity -> String -> IsaType ->
    VName -> [IsaPattern] -> IsaTerm -> Named Sentence
makeSentence k a d y df ps tx =
  makeNamed d $ ConstDef $ (if tx == xDummy
    then IsaEq xDummy $ xDummy
    else let w = ( case k of
               InstDef -> dispMN y
               FunDef  -> hideNN y )
         in IsaEq (Const df w) $ termMAbs a ps tx)

------------------- transIMatch auxs ---------------------------------

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

--------------- other theory trans auxs ----------------------------------
-- annotated translation function.
-- Each parameter pattern - IsaPattern - associated
-- with datatype information - [(String,Int)]
-- case variable name - IsaTerm
-- parameter name before translation - String
transMultiDef :: Continuity -> ConstTab -> [([PrPat], IsaTerm)]
    -> [([([(String, Int)],((IsaTerm, String), IsaPattern))], IsaTerm)]
transMultiDef c sign ls =
  let
   ws = csAris [fst w | w <- ls]
   ks = [([newInfo v | v <- xs], y) | (xs, y) <- ls]
   ss = map standizeVars ks
 in [(zipNE ws rs, s) | (rs,s) <- ss]
 where
  newInfo f = (snd $ extCI f, transPat c sign f)
  zipNE ws rs = case ws of
    [] -> []
    hd : xs -> (case hd of
           [] -> []
           _ -> if rs == [] then error "Hs2HOLCF, zipNE"
                else [(hd, head rs)]) ++ zipNE xs (tail rs)

-- Extract datatype information from a list of patterned parameter lists.
-- Returns the list of constructors and arities for parameter datatypes.
csAris :: [[PrPat]] -> [[(String,Int)]]
csAris ws = let
   ls = removeEL ws
 in case ls of
   [] -> []
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
   []    -> snd m
   h : _ -> let
      k1s = map fst ls
      xs  = map head (filter (/= []) k1s)
      xxs = remove_duplicates [((snd $ fst $ snd x, snd $ snd x),
                [(us,t) | (u:us,t) <- ls, u == x] ++
                     [(us,t) | ((_,(_,Free _)):us,t) <- ls]) | x <- xs]
      ws = remove_duplicates
                 $ [((a,b),formCaseExp ct c) | ((a,b),c) <- xxs]
    in makeCase (fst $ fst $ snd h) $ map (\z -> trCase ct z ws) (fst h)
 where
  makeCase t lst = Case t lst

------------------------ TERM translation --------------------------------
------------------------ Patterns ----------------------------------------

transPat :: Continuity -> ConstTab -> PrPat -> IsaPattern
transPat a c t = let
        a' = if a == IsCont True then IsCont False else a
  in maybe xDummy id $ transMPat a' c t

transMPat :: Continuity -> ConstTab -> PrPat -> Maybe IsaPattern
transMPat = transMPatX False

transMPatX :: Bool ->
   Continuity -> ConstTab -> PrPat -> Maybe IsaPattern
transMPatX bx a' cs t = let
   tInt = IsaSign.Type "int" holType []
   a = if a' == IsCont True then IsCont False else a'
  in case t of
    TiDecorate.Pat p -> case p of
       HsPLit _ (HsInt n) -> return $ liftExp a (show n) tInt
       HsPList _ xs -> do
                  ws <- mapM (transMPatX bx a cs) xs
                  return $ foldr (termBAppl a $ consPT a) (nilPT a) ws
       _ -> transP a (mkVName . showIsaName) (transMPat a cs) p
    TiDecorate.TiPSpec w lt bb -> case w of
         HsVar x -> case (showIsaName x) of
            "errorH" -> Just $ bottomPT a
            _       -> transHV bx a x bb lt
         HsCon x -> transCN a x
    TiDecorate.TiPTyped x _ -> transMPat a cs x
    TiDecorate.TiPApp w z -> do w1 <- transMPat a cs w
                                z1 <- transMPat a cs z
                                return $ (termMAppl a w1 [z1])

transP :: IsaName i => Continuity -> (i -> VName) ->
      (p -> Maybe IsaPattern) -> (PI i p) -> Maybe IsaPattern
transP a trId trP p =
 case mapPI3 trId trP p of
   Just (HsPId (HsVar _))  -> return $ conDouble "DIC"
   Just (HsPTuple _ xs)    -> return $ Tuplex xs a
   Just (HsPParen x)       -> return x
   Just HsPWildCard        -> return $ Free $ mkVName "wildcX"
   _                       -> Nothing

-------------------------- Terms --------------------------------------

transExp :: Continuity -> ConstTab -> PrExp -> IsaTerm
transExp a c t = maybe xDummy id $ transMExp a c t

transMExp :: Continuity -> ConstTab -> PrExp -> Maybe IsaTerm
transMExp a cs t = let
   tInt = IsaSign.Type "int" holType []
   tRat = IsaSign.Type "Rat" holType []
  in case t of
    (TiPropDecorate.Exp e) -> case e of
       HsLit _ (HsInt n) -> return $ liftExp a (show n) tInt
       HsLit _ (HsFloatPrim n) -> return $ liftExp a (show n) tRat
       HsLit _ (HsString n) -> return $ liftStr a (show n)
       HsList xs -> do
               ws <- mapM (transMExp a cs) xs
               return $ foldr (termBAppl a $ consPT a) (nilPT a) ws
       HsLet (TiPropDecorate.Decs ds _) k -> do
          w <- mapM (transPatBind False a cs) ds
          z <- transMExp a cs k
          return $ Let w z
       HsCase e' as -> do
          e1 <- transMExp a cs e'
          bs <- transCases a cs (map extPE as)
          return $ Case e1 bs
       _ -> transE a (mkVName . showIsaName) (transMExp a cs)
                                     (transMPat a cs) e
    TiPropDecorate.TiSpec w st bb -> case w of
       HsVar x -> case (showIsaName x) of
           "errorH" -> Just $ bottomPT a
           _       -> transHV False a x bb st
       HsCon x -> transCN a x
    TiPropDecorate.TiTyped x _ -> transMExp a cs x

transE :: Continuity -> (PNT -> VName) -> (e -> Maybe IsaTerm)
       -> (p -> Maybe IsaPattern) -> (EI PNT e p j h k) -> Maybe IsaTerm
transE c trId trE trP e =
 case (mapEI5 trId trE trP e) of
   Just (HsId (HsVar _))              -> return $ conDouble "DIC"
   Just (HsApp x y)                   -> return $ if x == bottomPT c
                                            then x
                                            else termMAppl c x [y]
   Just (HsLambda ps x)               -> return $ termMAbs c ps x
   Just (HsIf x y z)                  -> return $ If x y z c
   Just (HsTuple xs)                  -> return $ Tuplex xs c
   Just (HsParen x)                   -> return x
   _                                  -> Nothing

----------------------- TERM auxs ----------------------------------------

liftExp :: Continuity -> String -> Typ -> IsaTerm
liftExp c n t = case c of
  IsCont _ -> App (conDouble "Def")
             (Const (mkVName n) $ hideNN t) NotCont
  NotCont -> Const (mkVName n) $ hideNN t

liftStr :: Continuity -> String -> IsaTerm
liftStr a n  = let
      st = Const (mkVName n) noType
   in case a of
        NotCont -> st
        IsCont _ -> termAppl liftString st

transCases :: Continuity -> ConstTab ->
    [(TiPat PNT, TiPropDecorate.TiExp PNT)] -> Maybe [(IsaTerm,IsaTerm)]
transCases r cs ks = case ks of
 [] -> return []
 _ : _ -> let
     cnn = extCL $ map fst ks -- (cons, arity) list for the case value.
     ys = [((snd $ extCI f, transPat r cs f), transExp r cs g)
                             | (f,g) <- ks] -- (cons, (ptn, exp)) list.
  in if null cnn then trace ("\n CASES: " ++ show ks) $
                      error "Hs2HOLCF.transCases"
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
  TiPApp m _                -> extCI m
  TiDecorate.Pat u          -> case u of
     HsPWildCard                -> ([],"wildcX")
     HsPParen p                 -> extCI p
     HsPLit _ (HsString "")     ->  ([],"emptyString")
     _                          -> ([], pp u)
  TiPTyped p _              ->  ([], pp p)
  _                         -> error "H2HOLCF.extCI"
 where
  gBN (UniqueNames.PN q _) = q

trCase :: Continuity -> (String, Int) ->
       [((String, IsaPattern), IsaTerm)] -> (IsaTerm, IsaTerm)
trCase r' h ys = let
     r = case r' of
           IsCont _ -> IsCont False
           _        -> r'
  in case ys of
    [] -> case r of
       IsCont _ -> (buildPat r h, bottomPT r)
       NotCont -> error "Hs2HOLCF.trCase"
    ((a, b), c) : as ->
       if a == fst h
       then repVsCPt b c (snd h)  -- snd h :: Int
       else if take 6 a == "wildcX"
       then (buildPat r h, c)
       else trCase r h as
 where
  mkpXVs = mkVs "pX"
  repVsCPt a b n = case a of
      IsaSign.Const _ _ -> (a, b)
      IsaSign.App x y@(IsaSign.Free _) z' -> let
             nv = mkpXVs n
             nr = renVars nv [y] b
             st = repVsCPt x nr (n-1)
             nf = termMAppl z' (fst st) [nv]
             ns = renVars nv [y] $ snd st
           in (nf, ns)
      _ -> trace ("\n print A: " ++ show a) $
           trace ("\n print B: " ++ show b) $
           error "Hs2HOLCF.repVsCPt"
  buildPat s (x, n) = let
     hh = string2iterm s x Nothing
     k = Const (mkVName $ showIsaName x) noTypeC
     j = maybe k id hh
     sk = termMAppl s j $ reverse $ map mkpXVs [1..n]
   in sk

extClass :: PNT -> Maybe String
extClass p  = case p of
  PNT _ (MethodOf (PN x _) _ _) _   -> Just x
  _                                 -> Nothing

transPatBindX :: Bool ->
    Continuity -> ConstTab -> PrPat -> PrExp -> Maybe (IsaTerm,IsaTerm)
transPatBindX b a cs p e = do
              x <- transMPatX b a cs p
              y <- transMExp a cs e
              return (x, y)

transPatBind :: Bool ->
    Continuity -> ConstTab -> PrDecl -> Maybe (IsaTerm,IsaTerm)
transPatBind b a cs s = case s of
  TiPropDecorate.Dec (PropSyntaxStruct.Base
      (HsDeclStruct.HsPatBind _ p (HsGuardsStruct.HsBody e) _)) ->
         transPatBindX b a cs p e
  _ -> error "HsHOLCF.transPatBind"

transCN :: Continuity -> PNT -> Maybe IsaTerm
transCN c x = let
     k = pp x
     y = showIsaName x
     w = Const (mkVName y) $ Hide noTypeT TCon (extArity x)
     zz = string2iterm c k Nothing
  in return $ maybe w id $ zz

extArity :: PNT -> Maybe Int
extArity p = case p of
  (PNT z (ConstrOf _ x) _) -> let
       y = pp z
       ls = [(gBN $ conName w, conArity w) | w <- constructors x]
       ns = Map.fromList ls
    in Map.lookup y ns
  _ -> Nothing
 where
  gBN (UniqueNames.PN q _) = q

transHV :: Bool -> Continuity -> PNT -> [HsType] ->
                HsScheme -> Maybe IsaTerm
transHV _ a x lt tt = let
      qq = pp x
      n  = showIsaName x
      xt = maybe noTypeT id $ transMScheme a tt
      kt = maybe noTypeT id $ case lt of
                       r:_ -> transMType a [] r
                       _   -> Nothing
      zt = replaceTyVar kt xt
      dx = case x of
         PNT (PN _ (UniqueNames.G _ _ _)) _ _ ->
                                    mkConstV n (hideNN zt)
         PNT (PN _ (UniqueNames.S _)) _ _     -> mkFree n
         PNT (PN _ (UniqueNames.Sn _ _)) _ _  -> mkFree n
         _                                    -> error "Hs2HOLCF.transHV"
      rt = maybe dx id $ string2iterm a qq (Just lt)
  in return rt

string2iterm :: Continuity -> String ->
                    Maybe [HsType] -> Maybe IsaTerm
string2iterm a qq ls =
   case (showIsaName qq) of
   "()"        -> return $ unitPT a
   "(,)"       -> return $ pairPT a
   "True"      -> return $ truePT a
   "False"     -> return $ falsePT a
   "conjH"     -> return $ andPT a
   "disjH"     -> return $ orPT a
   "notH"      -> return $ notPT a
   ":"         -> return $ consPT a
   "[]"        -> return $ nilPT a
   "Nothing"   -> return $ nothingPT a
   "Just"      -> return $ justPT a
   "fstH"      -> return $ fstPT a
   "sndH"      -> return $ sndPT a
   "headH"     -> return $ headPT a
   "tailH"     -> return $ tailPT a
   "Left"      -> return $ leftPT a
   "Right"     -> return $ rightPT a
   "return"    -> return $ mkTyConst a ls "return"
   "mbind"     -> return $ mkTyConst a ls "mbind"
   "mbbind"    -> return $ mkTyConst a ls "mbbind"
   _           -> Nothing
   where
   mkTyConst aa tt s = let
     ndf = (case tt of
        Just (x:_) -> (let
               w = typeId $ extHead $ transType aa [] x
           in s ++ "_" ++ w)
        _ -> s)
     in Const (mkVName ndf) noType

----------------------- TERM trans recursive schemes ---------------------

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

-------------------------------------------------------------------------
------------------------ SIGNATURE translation --------------------------
-------------------------------------------------------------------------

transSignature :: Continuity -> Bool -> HatAna.Sign -> Result IsaSign.Sign
transSignature c m sign =  let
     tys  = HatAna.types sign
     vals = HatAna.values sign
     xx   = getDomainTab c vals
     nsig = IsaSign.emptySign
       { baseSig = case (c,m) of
                   (IsCont _,False) -> HsHOLCF_thy
                   (NotCont,False) -> HsHOL_thy
                   (IsCont _,True) -> MHsHOLCF_thy
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
   in Result [] $ Just nsig

------------------------------ TYPE translation -------------------------
{- signature translation takes after one to Stratego, relies
  on Isabelle.Translation to solve naming conflicts. -}

transType :: Continuity -> [HsType] -> HsType -> IsaType
transType a c t = maybe noTypeT id $ transMType a c t

transMType :: Continuity -> [HsType] -> HsType -> Maybe IsaType
transMType a c (Typ t) = transT a
        (transIdV a c) (transIdC a) (transMType a c) t

transT :: Show d => Continuity -> (PNT -> Maybe IsaType)
       -> (PNT -> Maybe IsaType) -> (d -> Maybe IsaType)
       -> TI PNT d -> Maybe IsaType
transT c trIdV trIdC trT t =
 case mapTI3 trIdV trIdC trT t of
    Just (HsTyFun t1 t2) -> return $ (case c of
              IsCont _ -> mkContFun t1 t2
              NotCont -> mkFunType t1 t2)
    Just (HsTyApp t1 t2) ->
       case t1 of
         IsaSign.Type name s args -> -- better resolve nested HsTyApp first
                    return $ IsaSign.Type name s $ args ++ [t2]
         _ -> Nothing
    Just (HsTyVar a) -> return a
    Just (HsTyCon k) -> return k
    _ -> Nothing

getSort :: Continuity -> [HsType] -> PNT -> IsaSort
getSort r c t = case c of
   [] -> case r of
             IsCont _ -> dom
             NotCont -> holType
   (x@(Typ (HsTyApp _ _))):cs -> let
               a = getInstType x
               b = getInstClass x
               d = getLitName a
               s = getSort r cs t
               k = transClass b
               u = showIsaName d
               v = showIsaName t
           in if u == v then k:s else s
   _:cs -> getSort r cs t

transIdV :: Continuity -> [HsType] -> PNT -> Maybe IsaType
transIdV a c t = return $ TFree (showIsaName t) (getSort a c t)

transIdC :: Continuity -> PNT -> Maybe IsaType
transIdC c t = case t of
 PNT _ (TypedIds.Class _ _) _ -> Nothing
 _ -> return $ let
    tfs = transFields c t
    srt = case c of
             IsCont _ -> dom
             NotCont -> holType
  in
  case (UniqueNames.orig t) of
    UniqueNames.G (PlainModule m) n _ ->
                  IsaSign.Type (transTN c m n) srt tfs
    UniqueNames.G (MainModule m) n _ ->
                  IsaSign.Type (transPath m n) srt tfs
    _ -> IsaSign.Type (showIsaName t) srt tfs

transFields :: Continuity -> PNT -> [IsaType]
transFields c t = let
     srt = case c of
             IsCont _ -> dom
             NotCont -> holType
  in case t of
    PNT _ (TypedIds.Type q) _ ->
          [TFree (showIsaS x) srt | (PN x _) <- TypedIds.fields q]
    PNT _ (TypedIds.FieldOf _ q) _ ->
          [TFree (showIsaS x) srt | (PN x _) <- TypedIds.fields q]
    _ -> []

mapTI3 :: (Show i1, Show i2, Show t1, Show t2) =>
        (i1 -> Maybe i2) -> (i1 -> Maybe i2) -> (t1 -> Maybe t2)
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
     _                  -> Nothing

------------------------------ Class translation ------------------------

transClass :: HsType -> IsaClass
transClass x = case x of
    Typ (HsTyCon c) -> IsaClass (showIsaName c)
    Typ _ -> trace ("\n CLASS: " ++ show x) $
             error "Hs2HOLCF.transClass"

-------------------------- SIGN fields translation -----------------------
-------------------------- translation for ConstTab ----------------------

getConstTab ::  Continuity -> VaMap -> ConstTab
getConstTab c = Map.map fst . Map.filter ((== IsaVal) . snd)
                . getAConstTab c

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

------------------------ translation of domaintab -----------------------

getDomainTab :: Continuity -> VaMap -> DomainTab
getDomainTab c f =  let
  ls = remove_duplicates
     [getDomainEntry (getAConstTab c f) x |
                                 x <- Map.keys f, checkTyCons x]
  in getDepDoms ls

getDomainEntry :: AConstTab -> HsId -> [DomainEntry]
getDomainEntry ctab t = case t of
  HsCon (PNT _ (TypedIds.ConstrOf _ d) _) ->
     [(getDomType ctab (mkVName $ showIsaName t),
       [(b, getFieldTypes ctab b)
           | b <- [ mkVName $ showIsaName c
                     | PN c _ <-  map conName (constructors d)]])]
  _ -> []

---------------------- translation for Classrel (from KEnv) ------------

getClassrel :: Continuity -> TyMap -> Classrel
getClassrel c f = liftMapByList Map.toList Map.fromList
                  (IsaClass . showIsaName) (transClassInfo c) f

transClassInfo :: Continuity -> (Kind, HsTypeInfo) -> Maybe [IsaClass]
transClassInfo c p = case snd p of
  TiTypes.Class _ _ _ _ ->
    Just $ remove_duplicates $ (case c of
                       IsCont _ -> dom
                       NotCont -> holType)
             ++ map transClass (extClassInfo $ snd p)
  _ -> Nothing

------------------- translation of Abbrs (from KEnv) --------------------

getAbbrs ::  Continuity -> TyMap -> Abbrs
getAbbrs c = Map.foldWithKey (\ k v -> case v of
           Nothing -> id
           Just p -> Map.insert k p) Map.empty
               . liftMapByList Map.toList Map.fromList
                  (showTyNm c) (transAbbrsInfo c)
    where showTyNm w t = case t of
            HsCon x -> case transIdC w x of
                    Just (IsaSign.Type n _ _) -> n
                    _ -> showIsaName t
            _ -> showIsaName t

transAbbrsInfo :: Continuity -> (Kind, HsTypeInfo) ->
                                   Maybe ([TName], IsaType)
transAbbrsInfo c p = case (snd p) of
  TiTypes.Synonym _ _ -> let (x, y) = extAbbrsInfo (snd p) in
      Just (map showIsaName x, transType c [] y)
  _ -> Nothing

---------------------- translation of arities ---------------------------

getArities :: Continuity -> DomainTab -> HsInstances -> IsaSign.Arities
getArities c dt db = Map.fromList (groupInst $ getTypeInsts c dt db)

getTypeInsts :: Continuity -> DomainTab -> HsInstances -> [IsaTypeInsts]
getTypeInsts c dt db =
    [(typeId $ transType c [] $ getMainInstType x,
                                             [transInst c x]) | x <- db]
    ++ [(u,[(IsaClass "Eq", [])]) | [(IsaSign.Type u _ [],_)] <- dt]

transInst :: Continuity -> HsInstance ->
                         (IsaClass, [(IsaType, [IsaClass])])
transInst c i = let (x, y) = prepInst i
                    w = case c of
                         IsCont _ -> pcpo
                         NotCont -> isaTerm
  in (transClass x,
      [(transType c [] a, w : map transClass b) | (a, b) <- y])

--------------------------------------------------------------------------
