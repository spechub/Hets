{- |
Module      :  $Header$
Copyright   :  (c) Paolo Torrini and Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from Haskell to Isabelle-HOLCF.

-}
{- todo
   use hana to look at outcome of Haskell files
   type is in: Haskell.Hatchet.MultiModuleBasics -- main datatype
               Haskell.Hatchet.Representation  - types, kinds, schemes
               Haskell.Hatchet.Env  -- environments

   look at Isabelle.IsaSign.hs
   write function transSignature below, 
     test it with
       hets -g file.hs
       click at node, select "Translate theory" or "Prove"
       select Haskell2IsabelleHOLCF
   write function transSentence below
-}


module Comorphisms.Haskell2IsabelleHOLCF where

--import Common.Lib.Parsec.Char as Char
import Logic.Logic
-- import Logic.Comorphism
-- import Common.Id
import Common.Result as Result
import qualified Common.Lib.Map as Map
-- import qualified Haskell.Hatchet.AnnotatedHsSyn as Annotated
import Data.List
import Data.Maybe
import Common.AS_Annotation (Named)
-- import Debug.Trace

-- Haskell
-- import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.MultiModuleBasics as MMB
--import qualified Haskell.Hatchet.MultiModuleBasics as MMB (ModuleInfo,
--                                          emptyModuleInfo,
--                                        joinModuleInfo)
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl,AHsName) 
import Haskell.Hatchet.FiniteMaps as FiniteMaps
import Haskell.Hatchet.Representation as Rep

-- Isabelle
import Isabelle.IsaSign as IsaSign
-- import Isabelle.Logic_Isabelle
-- import Isabelle.IsaPrint

-- | The identity of the comorphism
data Haskell2IsabelleHOLCF = Haskell2IsabelleHOLCF deriving (Show)

instance Language Haskell2IsabelleHOLCF -- default definition is okay

{-
instance Comorphism Haskell2IsabelleHOLCF -- multi-parameter class Com.
               Haskell Haskell_Sublogics
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = Haskell
    sourceSublogic _ = Haskell_SL
                       { has_sub = False,   -- subsorting
                         has_part = True,  -- partiality
                         has_eq = True,    -- equality
                         has_pred = True,  -- predicates
                         has_ho = True,  -- higher order
                         has_type_classes = False,
                         has_polymorphism = False
                         has_type_constructors = False,  which_logic = HOL
                       }
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_sign _ = transSignature

    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign phi =
            Just $ Sentence {senTerm = (transSentence sign phi)}
    --map_symbol :: cid -> symbol1 -> Set symbol2

-}
---------------------------- Signature -----------------------------

-- The args of Sign can be accessed by selector functions,
-- defined for each object.  
--
-- data Sign = Sign { baseSig :: String, -- like Pure, HOL etc.
--                    tsig :: TypeSig,
--                    constTab :: Map.Map String Typ,
--                    syn :: Syntax
--                  }

-- Check the MultiModuleBasics.hs where ModuleInfo is defined.
-- There is an import of AnnotatedHsSyn, containing the actual Haskell abstract
-- syntax. 
--
-- (the translation functions here refer to HasCASL.Le via 
-- parameters such as typeInfo and typeDefn. This reference is ok for HasCASL,
-- not for Haskell)

-- 
-- see Common/Result.hs.
-- needs to be done! Below, just the HasCASL code!!!
-- transSignature, from sign::ModuleInfo -MultiModuleBasics-, 
-- returns a Just(Sign,[])::Result(Sign, [Named Sentence]) -Result-
-- 
--        emptyTypeSig 
--            {tycons = Map.fromList (fm2map . kinds sign))},
--        emptyTypeSig 
--            {tycons = Map.fromList (extractMap (tyconsMembers sign))},
--   tycons:: Map String Int -IsaSign-
--        Map.foldWithKey (insertOps datatypeList)    
--                               Map.empty 
--                               (fm2map . varAssumps sign),
--

-- type AHsName = 

fm2map :: Ord k => FiniteMaps.FiniteMap k a -> Map.Map k a
fm2map f = Map.fromList $ FiniteMaps.toListFM f
-- maybe better using envToList instead of fmToList, see Env.hs

mychr :: Int -> Char
mychr n = 'n'

transSignature :: MMB.ModuleInfo
                   -> Result.Result(IsaSign.Sign,[Named IsaSign.Sentence]) 

transSignature sign = transSignature1 ["var"++ [mychr n] | n <- [1 ..] ] sign

type NewNames = [String]

transSignature1 :: NewNames -> MMB.ModuleInfo
                   -> Result.Result(IsaSign.Sign,[Named IsaSign.Sentence]) 

transSignature1 ns sign = let datatypeList = transDatatype ns (tyconsMembers sign) (FiniteMaps.toListFM $ dconsAssumps sign) in 
 Result.Result 
  [] 
  (Just ( IsaSign.Sign{
    baseSig = "MainHC",
    tsig = emptyTypeSig 
            {tycons = Map.foldWithKey (extractTypeName (tyconsMembers sign)) 
                                      Map.empty 
                                      (fm2map $ kinds sign)},
    constTab = Map.fromList $ extractConsts datatypeList,
    dataTypeTab = [], 
    domainTab = inDearrowize datatypeList,
    showLemmas = False,
    syn = () },
    [] ))                                 -- for now, no sentences
 where 
    extractTypeName list name kind m = 
        let n = show name 
            ls = [show x | (x,_) <- list]                               
        in 
        if (elem n ls) then Map.insert n (arity kind) m
                         else m
    arity k = case k of 
                   Rep.Star -> 0
                   (Rep.Kfun _ k2) -> 1 + arity k2
                   (Rep.KVar _) -> 0
--    insertOps dtlist name scheme m = Map.insert (show name) (findType dtlist scheme) m

    
s1Datatype :: [(AHsName, [AHsName])] -> [(AHsName,Scheme)] -> [[(String, Type)]]
s1Datatype list1 list2 = [[(show a, extractType b) | (a,b) <- list2, elem a ls] | (_,ls) <- list1] 

-- equivalent !!!
-- pDatatype :: [(AHsName, [AHsName])] -> [(AHsName,Scheme)] -> [[(String, Type)]]
-- pDatatype list1 list2 = [[(show a, extractType b) | (a,b) <- list2, extractType b = TArrow c d, show d = show dtName] | (dtName,_) <- list1] 

s2Datatype :: [(String, Type)] -> (Type, [(String, Type)]) 
s2Datatype ls = 
            case ls of ((a,TArrow b c):rest) -> (c,(a,TArrow b c):rest)  

s3Datatype :: [[(String, Type)]] -> [(Type, [(String, Type)])] 
s3Datatype list = map s2Datatype list  

s4Datatype :: [(AHsName, [AHsName])] -> [(AHsName,Scheme)] -> [(Type,[(String, Type)])]
s4Datatype list1 list2 = s3Datatype (s1Datatype list1 list2)

checkDep1 ::  Type  -> [Type] -> Bool
checkDep1 a ls = case ls of b:bs -> if subTypeFormula a b then True else checkDep1 a bs
                            [] -> False

-- symmetric
checkDep2 :: (Type,[(String, Type)]) -> (Type,[(String, Type)]) -> Bool 
checkDep2 a b = if checkDep1 (fst a) (map snd (snd b)) || checkDep1 (fst b) (map snd (snd a)) then True else False

checkDep3 :: (Type,[(String, Type)]) -> [(Type,[(String, Type)])] -> Bool
checkDep3 a ls = case ls of b:bs -> if checkDep2 a b then True else checkDep3 a bs
                            [] -> False

-- symmetric, by def of checkDep2
checkDep4 :: [(Type,[(String, Type)])] -> [(Type,[(String, Type)])] -> Bool
checkDep4 ls bs = case ls of a:as -> if checkDep3 a bs then True else checkDep4 as bs
                             [] -> False

--checkDep5 ::  ([[(Type,[(String, Type)])]], [[(Type,[(String, Type)])]]) -> [[(Type,[(String, Type)])]]
--checkDep5 ls cs = case ls of (a:as,b:bs) -> if (checkDep4 a b) then (checkDep5 ((a ++ b):as, bs) cs) else checkDep5 (a:as, bs) (b:cs)
--                            (_:as,[]) -> checkDep5 (as,cs) []
--                            ([],_) -> snd ls 

checkDep5 ::  [[(Type,[(String, Type)])]] -> [[(Type,[(String, Type)])]] -> [[(Type,[(String, Type)])]] -> [[(Type,[(String, Type)])]]
checkDep5 ls ms cs = case ls of 
                         a:as -> case ms of 
                                   b:bs -> if checkDep4 a b then checkDep5 ((a ++ b):as) bs cs else checkDep5 (a:as) bs (b:cs)
                                   [] -> checkDep5 as cs []
                         [] -> ms 

--checkDep5 ::  [[(Type,[(String, Type)])]] -> [[(Type,[(String, Type)])]] -> [[(Type,[(String, Type)])]]
--checkDep5 ls ms cs = case ls of 
--                         a:as -> if ms == [] then checkDep5 as cs [] else  
--                                  let b = head $ tail ms 
--                                      bs = tail ms in  
--                                      if checkDep4 a b then checkDep5 ((a ++ b):as) bs cs else checkDep5 (a:as) bs (b:cs)
--                         [] -> ms 

--checkDep5 a:as b:bs cs = if checkDep4 a b then checkDep6 (join a b):as bs cs else checkDep5 a:as bs b:cs
--checkDep5 a:as [] cs = checkDep5 as cs []
--checkDep5 [] bs cs = bs 

checkDep6 :: [[(Type,[(String, Type)])]] -> [[(Type,[(String, Type)])]]
checkDep6 a = checkDep5 (tail a) [head a] []

singList :: [a] -> [[a]]
singList list = [[a] | a <- list]

prepDatatype :: [(AHsName, [AHsName])] -> [(AHsName,Scheme)] -> [[(Type, [(String, Type)])]]
prepDatatype a b = checkDep6 $ singList $ s4Datatype a b


subTypeFormula :: Type -> Type -> Bool
subTypeFormula t1 t2 = if t1 == t2 then True else
                          case t2 of Rep.TVar _ -> False
                                     Rep.TCon _ -> False
                                     Rep.TGen _ -> False
                                     Rep.TAp u v -> subTypeFormula t1 u || subTypeFormula t1 v 
                                     Rep.TArrow u v -> subTypeFormula t1 u || subTypeFormula t1 v 
                                     Rep.TTuple (a:rest) -> subTypeFormula t1 a || subTypeFormula t1 (TTuple rest) 


extractType :: Scheme -> Type
extractType (Forall _ (_ :=> t)) = t 
-- extractType (Forall kindList (predList :=> t)) = t 

--extractPreds :: Scheme -> [Pred]
--extractPreds (Forall kindList (predList :=> t)) = predList 

gDomProduct :: [Typ] -> Typ
gDomProduct as = case as of a:rest -> mkDomProduct a (gDomProduct rest)
                            [a] -> a
                            [] -> voidDom
 
trType :: Type -> VarName Typ
trType t
   = case t of
           Rep.TVar _ ->     do findResult <- lookupInMap t 
                                case findResult of
                                      Nothing -> do nm <- nextName
                                                    updateVMap (t, nm)
                                                    return $ IsaSign.TFree nm domain
                                      Just v  -> return $ IsaSign.TFree v domain 
           Rep.TCon tycon -> return $ IsaSign.Type (show tycon) domain []
           Rep.TAp t1 t2  -> do a1 <- trType t1
                                a2 <- trType t2
                                return $ mkDomAppl a1 a2 
           Rep.TGen _     -> do findResult <- lookupInMap t 
                                case findResult of
                                      Nothing -> do nm <- nextName
                                                    updateVMap (t, nm)
                                                    return $ IsaSign.TFree nm domain
                                      Just v  -> return $ IsaSign.TFree v domain
           Rep.TArrow t1 t2 -> do a1 <- trType t1
                                  a2 <- trType t2
                                  return $ mkContFun a1 a2
           Rep.TTuple ts    -> do nts <- mapM trType ts
                                  return $ gDomProduct nts

transT10 :: [(String, Type)] -> VarName [(String, Typ)]
transT10 xs = case xs of (n,a):rs -> do b <- trType a
                                        ls <- transT10 rs
                                        return ((n,b) : ls) 
                         [] -> return []

transT11 :: (Type, [(String, Type)]) -> VarName (Typ, [(String, Typ)])
transT11 xs = case xs of (a,ls) -> do t <- trType a
                                      ms <- transT10 ls
                                      return (t,ms)
--                         (_,[]) -> return []

transT12 :: [(Type, [(String, Type)])] -> VarName [(Typ, [(String, Typ)])]
transT12 xs = case xs of (a:ls) -> do t <- transT11 a
                                      ms <- transT12 ls
                                      return (t:ms)
                         [] -> return []

transT13 :: [[(Type, [(String, Type)])]] -> VarName [[(Typ, [(String, Typ)])]]
transT13 xs = case xs of (a:ls) -> do t <- transT12 a
                                      ms <- transT13 ls
                                      return (t:ms)
                         [] -> return []

transDatatype :: [String] -> [(AHsName, [AHsName])] -> [(AHsName,Scheme)] -> [[(Typ, [(String, Typ)])]]
transDatatype ns a b = let (VarName s) = transT13 $ prepDatatype a b in (fst $ s (State [] ns)) 

dearrowize :: Typ -> [Typ]
--dearrowize (Type ("dFun" _ [b,c])) = b:(dearrowize c)
--dearrowize a = [a] 
dearrowize a = case a of (Type "dFun" _ [b,c])   -> b:(dearrowize c)
                         _            -> [a] 

inDearrowize ::  [[(Typ, [(String, Typ)])]] -> [[(Typ, [(String, [Typ])])]]
inDearrowize ls = map (\x -> map (\y -> (fst y, map (\z -> (fst z, dearrowize $ snd z)) (snd y))) x) ls

remove_duplicates :: (Eq a) => [a] -> [a]
remove_duplicates ls = remove_dupes ls []

remove_dupes :: (Eq a) => [a] -> [a] -> [a]
remove_dupes ls ms = case ls of x:rs -> if (elem x (rs ++ ms)) then remove_dupes rs ms
                                                                   else remove_dupes rs (x:ms)
                                [] -> ms

extractConsts :: [[(Typ, [(String, Typ)])]] -> [(String, Typ)]
extractConsts ls = remove_duplicates $ concat $ concat (map (map snd) ls) 



{-
data PType = PTVar (Type,String)
           | PTCon (Type,String)
           | PTAp  PType PType
           | PTArrow PType PType
           | PTTuple [PType]
             deriving (Eq, Show)

prettyType :: Type -> VarName PType
prettyType t
   = case t of
           TVar tyvar -> do findResult <- lookupInMap t 
                            case findResult of
                               Nothing -> do nm <- nextName
                                             updateVMap (t, nm)
                                             return $ PTVar (t, nm)
                               Just v  -> return $ PTVar (t, v) 
           TCon tycon -> return $ PTCon (t, show tycon)
           TAp t1 t2  -> return $ PTAp (prettyType t1) (prettyType t2) 
           TGen i     -> do findResult <- lookupInMap t 
                            case findResult of
                               Nothing -> do nm <- nextName
                                             updateVMap (t, nm)
                                             return $ PTVar (t, nm)
                               Just v  -> return $ PTVar (t, v) 
           TArrow t1 t2 -> return PTArrow (prettyType t1) (prettyType t2)
           TTuple ts    -> do nts <- mapM prettyType ts
                              return $ PTTuple nts


trType :: Type -> Typ
trType t =   case t of TVar a -> TFree (show a, dom)
                       TCon a -> Type (show a, dom, [])
                       TAp a b -> mkTypeAppl (trType a) (trType b))
                       TGen a -> TFree (show a, dom)
                       TArrow a b -> mkContFun (trType a) (trType b)
                       TTuple as -> gDomProduct as

-}

-- ... go on. possible problem: the assumptions that must be derived from
-- the predicates. Care: the Haskell classes must be mapped into IsaClasses.
-- 
-- As it is now, all the class information in Haskell goes lost !!!
-- and the problem is more in transType than in trType.
-- Need to translate infomration about classes, ie the output of extractPreds.
--
-- or maybe relying on class hierarchy is enough??
--
--     extractMap m = map extractNA m
--     extractNA a = (show . fst a, length . snd a)
-- showIsa::Id->String  -IsaPrint-
-- insertOps::OpName->OpInfos->Map->Map
-- opInfos::OpInfos->[OpInfo]    -Le-
-- ...
-- filters types that are not datatypes
--    isDatatypeDefn t = case typeDefn t of
--                  DatatypeDefn _ -> True
--                  _              -> False
{-
    insertOps opName opInfs m = 
     let opIs = opInfos opInfs   
     in if (length opIs) == 1 then
          let transOp = transOpInfo (head opIs)  --transOp
          in case transOp of 
               Just op -> Map.insert (showIsa opName) op m
               Nothing -> m
          else 
            let transOps = map transOpInfo opIs     -- transOps
            in  foldl (\m1 (transOp,i) -> 
                           case transOp of
                             Just typ -> Map.insert (showIsaI opName i) 
                                                     typ m1
                             Nothing   -> m1)
                       m
                       (zip transOps [1..length transOps])


-- NoOpDefn is for the case when the operator is just declared, not defined
-- 
transOpInfo :: OpInfo -> Maybe Typ
transOpInfo (OpInfo opT _ opDef) = 
  case opDef of
    NoOpDefn Pred   -> Just (transPredType opT)  -- ??
    NoOpDefn _      -> Just (transOpType opT)    -- ??
    ConstructData _ -> Nothing                   -- ??
    _               -> error "[Comorphims.Haskell2IsabelleHOLCF] Not supported operation declaration and/or definition"


transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ op _) = transType op


transPredType :: TypeScheme -> Typ
transPredType  (TypeScheme _ pre _) = 
       case pre of
         FunType tp _ _ _ -> (transType tp) --> boolType   -- see IsaSign
         _                -> 
           error "[Comorphims.Haskell2IsabelleHOLCF] Wrong predicate type"


transType :: Type -> Typ

transType (Tvar tyvar) =
   case tyvar of
      Tyvar (_ _ AHsSymbol string) Kind -> TFree (string, transKind Kind)
      _ -> error "[Comorphims.Haskell2IsabelleHOLCF] not a variable"

transType (TCon tycon) =
   case tycon of
      Tycon 

-}


{-
-- As.Type         HasCASL types
-- Representation.Type    Haskell types
-- IsaSign.Typ     Isabelle types
transType :: Type -> Typ
transType (TypeName typeId _ i) = if i == 0 then Type(showIsa typeId,[])
                                    else TVar((showIsa typeId,0),[])
transType (ProductType types _) = foldl1 IsaSign.mkProductType 
                                         (map transType types)
transType (FunType type1 arr type2 _) = 
  case arr of
    PFunArr -> (transType type1) --> (mkOptionType (transType type2))
    FunArr  -> (transType type1) --> (transType type2)
    _       -> 
      error "[Comorphims.Haskell2IsabelleHOLCF] Not supported function type"
transType (TypeAppl type1 type2) = Type("typeAppl", [transType type1] ++ [transType type2])
transType _ = error "[Comorphims.Haskell2IsabelleHOLCF] Not supported type"
-}




{-

transDatatype :: TypeMap -> DataTypeTab
transDatatype tm = map transDataEntry (Map.fold extractDataypes [] tm)

extractDataypes :: TypeInfo -> [DataEntry] -> [DataEntry]
extractDataypes ti des = case typeDefn ti of
                           DatatypeDefn de -> des++[de]
                           _               -> des

transDataEntry :: DataEntry -> DataTypeTabEntry
transDataEntry (DataEntry _ tyId Le.Free tyArgs alts) = 
                         [((mkDName tyId tyArgs), (map mkAltDefn alts))]
transDataEntry _ = 
  error "[Comorphims.Haskell2IsabelleHOLCF] Not supported datatype definition"

mkDName :: TypeId -> [TypeArg] -> Typ
mkDName tyId tyArgs = Type(showIsa tyId,(map transTypeArg tyArgs)) --Type("typeAppl",(Type(showIsa tyId,[])):(map transTypeArg tyArgs)) --

transTypeArg :: TypeArg -> Typ
transTypeArg (TypeArg tyId _ _ _) = TVar((showIsa tyId,0),[])

mkAltDefn :: AltDefn -> DataTypeAlt
mkAltDefn (Construct opId types Total _) = 
   let typs = map transType types
   in case opId of
        Just opI -> (showIsa opI, typs)
        Nothing  -> ("", typs)
mkAltDefn (Construct _ _ Partial _) = error "[Comorphims.Haskell2IsabelleHOLCF] Not supported alternative definition in (free) datatype"


------------------------------ Formulas ------------------------------

transVar :: Var -> String
transVar = showIsa


transSentence :: Env -> Le.Sentence -> IsaSign.Term
transSentence e s = case s of
    Le.Formula t      -> transTerm e t
    DatatypeSen l     -> con "Ich bin gar kein richtiges Axiom..." -- transDataEntryAx (head l)
    ProgEqSen _ _ _pe -> 
      error "[Comorphims.Haskell2IsabelleHOLCF] transSentence: program"


transTerm :: Env -> As.Term -> IsaSign.Term
transTerm _ (QualVar (VarDecl var typ _ _)) = 
    let tp = transType typ 
        otp = tp --> mkOptionType tp
     in  (conSomeT otp) `App` IsaSign.Free(transVar var, tp)
transTerm _ (QualOp _ (InstOpId opId _ _) _ _)
  | opId == trueId =  con "True"
  | opId == falseId = con "False"
  | otherwise = conSome `App` con (getNameOfOpId opId)
transTerm sign (ApplTerm term1 term2 _) =
  testTerm term1
  where
--  trace ("Constructors?? "++ show (ApplTerm term1 term2 p) ++ "\n")
   testTerm t =
     case t of
       QualOp Fun (InstOpId opId _ _) _ _ -> transLog sign opId term1 term2 
       QualOp Pred _ _ _ -> con "pApp" 
                              `App` (transTerm sign term1) 
                              `App` (transTerm sign term2)
       QualOp Op _ typeScheme _ -> if isPart typeScheme then mkApp "app"
                                                        else mkApp "apt"
       ApplTerm t1 _ _ -> testTerm t1
       _                 -> mkApp "app"
     where mkApp s = con s 
                                 `App` (transTerm sign term1) 
                                 `App` (transTerm sign term2)
           isPart (TypeScheme _ op _) = 
             case op of
               FunType _ PFunArr _ _ -> True
               FunType _ FunArr _ _  -> False
               _                     -> 
                 error "[Comorphims.Haskell2IsabelleHOLCF] Wrong operation type"
transTerm sign (QuantifiedTerm quan varDecls phi _) = 
  foldr (quantify quan) 
        (transTerm sign phi) 
        (map toPair varDecls)
transTerm sign (TypedTerm term _ _ _) = transTerm sign term
transTerm sign (LambdaTerm pats part body _) =
  case part of
    Partial -> lambdaAbs transTerm
    Total   -> lambdaAbs transTotalLambda
  where 
   lambdaAbs f =
    if (null pats) then conSome 
                          `App` Abs(IsaSign.Free("dummyVar",dummyT), 
                                    dummyT, 
                                    (f sign body))
      else conSome `App` (foldr (abstraction sign) 
                                (f sign body)
                                pats)
transTerm sign (LetTerm Let eqs body _) = 
  transTerm sign (foldr let2lambda body eqs)
transTerm sign (TupleTerm terms _) =
  foldl1 (binConst pairC) (map (transTerm sign) terms)
transTerm sign (CaseTerm term pEqs _) = 
--  trace ("pEqs " ++ show pEqs ++ "\n")
  let alts = arangeCaseAlts sign pEqs
  in
    case term of
      QualVar (VarDecl decl _ _ _) -> Case (IsaSign.Free(transVar decl, dummyT), alts)
      _                            -> 
              Case (transTerm sign term,
                    (con "None", con "None"):
                    [(conSome `App` IsaSign.Free("caseVar", dummyT),
                      Case (IsaSign.Free("caseVar", dummyT), alts))])
transTerm _ _ = 
  error "[Comorphims.Haskell2IsabelleHOLCF] Not supported (abstract) syntax."

transTotalLambda :: Env -> As.Term -> IsaSign.Term
transTotalLambda _ (QualVar (VarDecl var typ _ _)) = 
  IsaSign.Free(transVar var, transType typ)
transTotalLambda _ (QualOp _ (InstOpId opId _ _) _ _)
  | opId == trueId =  con "True"
  | opId == falseId = con "False"
  | otherwise = con (getNameOfOpId opId)
transTotalLambda sign (ApplTerm term1 term2 _) = (transTotalLambda sign term1) `App` (transTotalLambda sign term2)
--   testTerm term1
--   where
-- --  trace ("Constructors?? "++ show (ApplTerm term1 term2 p) ++ "\n")
--    testTerm t =
--      case t of
--        QualOp Fun (InstOpId opId _ _) _ _ -> transLog sign opId term1 term2 
--        QualOp Pred _ _ _ -> con "pApp" 
--                               `App` (transTerm sign term1) 
--                               `App` (transTerm sign term2)
--        QualOp Op _ typeScheme _ -> if isPart typeScheme then mkApp "app"
--                                                         else mkApp "apt"
--        ApplTerm t1 _ _ -> testTerm t1
--        _                 -> mkApp "app"
--      where mkApp s = con s 
--                                  `App` (transTerm sign term1) 
--                                  `App` (transTerm sign term2)
--            isPart (TypeScheme _ op _) = 
--              case op of
--                FunType _ PFunArr _ _ -> True
--                FunType _ FunArr _ _  -> False
--                _                     -> 
--                  error "[Comorphims.Haskell2IsabelleHOLCF] Wrong operation type"
-- transTerm sign (QuantifiedTerm quan varDecls phi _) = 
--   foldr (quantify quan) 
--         (transTerm sign phi) 
--         (map toPair varDecls)
transTotalLambda sign (TypedTerm term _ _ _) = transTotalLambda sign term
transTotalLambda sign (LambdaTerm pats part body _) =
  case part of
    Partial -> lambdaAbs transTerm
    Total   -> lambdaAbs transTotalLambda
  where 
   lambdaAbs f =
    if (null pats) then Abs(IsaSign.Free("dummyVar",dummyT), 
                                    dummyT, 
                                    (f sign body))
      else  (foldr (abstraction sign) 
                                (f sign body)
                                pats)
transTotalLambda sign (LetTerm Let eqs body _) = 
  transTotalLambda sign (foldr let2lambda body eqs)
transTotalLambda sign (TupleTerm terms _) =
  foldl1 (binConst isaPair) (map (transTotalLambda sign) terms)
transTotalLambda sign (CaseTerm term pEqs _) = 
--  trace ("pEqs " ++ show pEqs ++ "\n")
  Case (transTotalLambda sign term, map transCaseAltTotal pEqs)
  where transCaseAltTotal (ProgEq pat term _) = 
                (transPat sign pat, transTotalLambda sign term)
transTotalLambda _ _ = 
  error "[Comorphims.Haskell2IsabelleHOLCF] Not supported (abstract) syntax."


transCaseEx :: Env -> As.Term -> IsaSign.Term
transCaseEx sign term =
  case term of
    QualVar (VarDecl decl _ _ _) -> IsaSign.Free(transVar decl, dummyT)
    _                            -> transTerm sign term


arangeCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
arangeCaseAlts sign pEqs = 
  let pats = map stripProgEq pEqs
  in
    case pats of
      (QualVar _):[] -> map (transCaseAlt sign) pEqs
      _              -> sortCaseAlts sign pEqs

sortCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
sortCaseAlts sign pEqs = 
  concat (map (unfoldCons sign) (map (groupCons pEqs) 
                                     (getCons sign (getName (head pEqs)))))

getName :: ProgEq -> TypeId
getName (ProgEq pat _ _) = 
  getTypeName pat 
  where getTypeName pat = case pat of
                            QualVar (VarDecl _ typ _ _) -> name typ
                            QualOp _ _ (TypeScheme _ typ _) _ -> name typ
                            TypedTerm _ _ typ _ -> name typ
                            ApplTerm  t _ _ -> getTypeName t
                            -- TupleTerm
        name t = case t of 
                   TypeName tyId _ 0 -> tyId
                   TypeAppl t _      -> name t
                   -- FunType t1 _ t2   -> 
                   -- ProductType
                   _                -> 
                      error "[Comorphims.Haskell2IsabelleHOLCF] Not supported type"


getCons :: Env -> TypeId -> [UninstOpId]
getCons sign tId = 
  sld (typeDefn (Map.find tId (typeMap sign)))
  where sld (DatatypeDefn (DataEntry _ _ _ _ altDefns)) =
          catMaybes (map ll altDefns)
        ll (Construct i _ _ _) = i


groupCons :: [ProgEq] -> UninstOpId -> [ProgEq]
groupCons pEqs name =  filter hasSameName pEqs
  where hasSameName (ProgEq pat _ _) = 
           hsn pat
        hsn pat =
          case pat of
            QualOp _ (InstOpId n _ _) _ _    -> n == name
            ApplTerm t1 t2 _  -> hsn t1
            TypedTerm t _ _ _ -> hsn t
            -- TupleTerm
            _                 -> False

unfoldCons :: Env -> [ProgEq] -> [(IsaSign.Term, IsaSign.Term)]
unfoldCons sign pEqs =
  let pats = map stripProgEq pEqs
  in
    if and (map noArgs pats) || and (map argIsVar pats) 
      then map (transCaseAlt sign) pEqs
        else substArg sign pEqs
  where noArgs t = case t of
                     QualOp _ _ _ _ -> True
                     QualVar _      -> True
                     _              -> False
        argIsVar pat = case pat of
                         ApplTerm _ t _  -> case t of
                                              QualVar _ -> True
                                              ApplTerm _ t _ -> argIsVar t
                                              _         -> False
                         QualVar _       -> True
                         TypedTerm t _ _ _ -> argIsVar t
                         -- TupleTerm
                         _               -> False

substArg :: Env -> [ProgEq] -> [(IsaSign.Term, IsaSign.Term)]
substArg sign pEqs =
  let frontCons = transPat sign (getFrontCons pEqs)
      varName = "consVar" ++ show (length pEqs)
      newPat = frontCons `App` IsaSign.Free(varName, dummyT)
      varId = (mkId [(mkSimpleId varName)])
      newVar = QualVar (VarDecl varId (TypeName varId MissingKind 1) Other [])
      newTerm = transTerm sign (CaseTerm newVar newPEqs [])
      newPEqs = map getNewPEqs pEqs
  in
     [(newPat, newTerm)]
  where getFrontCons ((ProgEq pat _ _):pEqs) = 
          case pat of 
            ApplTerm t _ _ -> t
            _              -> pat
        getNewPEqs (ProgEq pat term p) =  
          case pat of
            ApplTerm _ t _ -> ProgEq t term p
            _              -> ProgEq pat term p
                                                 
--  VarDecl Var Type SeparatorKind [Pos]

stripProgEq :: ProgEq -> Pattern
stripProgEq (ProgEq pat t pos) = case pat of
                                 TypedTerm p _ _ _ -> stripProgEq (ProgEq p t pos)
                                 -- TupleTerm      ->
                                 _                 -> pat


-- -- grep the names of all constructors
-- grepCons :: [Pattern] -> [InstOpId]
-- grepCons pats =
--   nub (catMaybes (map allCons pats))
--   where allCons pat =
--           case pat of
--             QualOp _ name _ _ -> Just (name)
--             ApplTerm t1 t2 _  -> allCons t1
--             TypedTerm t _ _ _ -> allCons t
--             QualVar _         -> Nothing
--             -- TupleTerm
--             _                 -> 
--               error "[Comorphims.Haskell2IsabelleHOLCF] Illegal case pattern."
 


{- todo
nested case patterns:
1. check if set of patterns is
1a. one pattern consisting of a variable => we are done
1b. set of constructor patterns 
    1b1. sort patterns according to leading constructor
    1b2. for each group of patterns with the same leading constructor
         1b2a. for each argument position, call 1. recursively

-}


transCaseAlt :: Env -> ProgEq -> (IsaSign.Term, IsaSign.Term)
transCaseAlt sign (ProgEq pat term _) = 
  (transPat sign pat, transTerm sign term)
   --Abs (transTerm sign pat, dummyT, transTerm sign term)

transPat :: Env -> As.Term -> IsaSign.Term
transPat _ (QualVar (VarDecl var _ _ _)) = IsaSign.Free(transVar var, dummyT)
transPat sign (ApplTerm term1 term2 _) = 
  (transPat sign term1) `App` (transPat sign term2)
transPat sign (TypedTerm term _ _ _) = transPat sign term
-- transPat sign (LambdaTerm pats Partial body _) =
--   if (null pats) then Abs(IsaSign.Free("dummyVar",dummyT), 
--                                         dummyT, 
--                                         (transPat sign body))
--      else foldr (abstraction sign) 
--                 (transPat sign body)
--                 pats
-- transPat sign (LetTerm Let eqs body _) = 
--   transPat sign (foldr let2lambda body eqs)
transPat sign (TupleTerm terms _) =
  foldl1 (binConst isaPair) (map (transPat sign) terms)
transPat _ (QualOp _ (InstOpId id _ _) _ _) = con (getNameOfOpId id)
transPat _ _ =  error "[Comorphims.Haskell2IsabelleHOLCF] Not supported (abstract) syntax."


let2lambda :: ProgEq -> As.Term -> As.Term
let2lambda (ProgEq pat term _) body = 
  ApplTerm (LambdaTerm [pat] Partial body [nullPos]) term [nullPos]


getType :: As.Term -> Typ
getType term = case term of
                    QualVar (VarDecl _ typ _ _) ->  transType typ
                    TypedTerm _ _ typ _ -> transType typ
                    TupleTerm terms _   -> evalTupleType terms
                    _ -> error "[Comorphims.Haskell2IsabelleHOLCF] Illegal pattern in lambda abstraction"
  where evalTupleType t = foldr1 IsaSign.mkProductType 
                                 (map getType t)

transLog :: Env -> Id -> As.Term -> As.Term -> IsaSign.Term
transLog sign opId opTerm term
  | opId == andId = foldl1 (binConst conj) 
                           (map (transTerm sign) ts)
  | opId == orId = foldl1 (binConst disj) 
                          (map (transTerm sign) ts)
  | opId == implId = binConst impl (transTerm sign t1)
                                   (transTerm sign t2)
  | opId == eqvId = binConst eqv (transTerm sign t1)
                                 (transTerm sign t2)
  | opId == notId = (con "Not") `App` (transTerm sign term)
  | opId == defId = defOp `App` (transTerm sign term)
  | opId == exEq = 
       binConst conj 
          (binConst conj 
              (binConst eq (transTerm sign t1) 
                           (transTerm sign t2))
               (defOp `App` (transTerm sign t1)))
          (defOp `App` (transTerm sign t2))
  | opId == eqId = binConst eq (transTerm sign t1)
                               (transTerm sign t2)
  | otherwise = (transTerm sign opTerm) `App` (transTerm sign term)
       where ts = getTerms term
             t1 = head ts
             t2 = last ts
             getTerms (TupleTerm terms _) = terms
             getTerms _ = error "[Comorphims.Haskell2IsabelleHOLCF] Incorrect formula coding in abstract syntax"


quantify :: Quantifier -> (Var,Type) -> IsaSign.Term -> IsaSign.Term
quantify q (v,t) phi  = 
  con (qname q) `App` Abs (con (transVar v), transType t, phi)
    where
      qname Universal   = "All"
      qname Existential = "Ex"
      qname Unique      = "Ex1"


abstraction :: Env -> As.Term -> IsaSign.Term -> IsaSign.Term
abstraction sign pat body = Abs((transTermAbs sign pat), getType pat, body)


transTermAbs :: Env -> As.Term -> IsaSign.Term
transTermAbs _ (QualVar (VarDecl var typ _ _)) = 
    IsaSign.Free(transVar var, transType typ)
transTermAbs sign (TupleTerm terms _) = foldl1 (binConst isaPair) 
                                               (map (transTermAbs sign) terms)
transTermAbs _ (QualOp _ (InstOpId opId _ _) _ _) = con (getNameOfOpId opId)
transTermAbs sign term = transTerm sign term

getNameOfOpId :: Id -> String
getNameOfOpId (Id [] _ _) = error "[Comorphims.Haskell2IsabelleHOLCF] Operation without name"
getNameOfOpId (Id (tok:toks) a b) = 
  if (tokStr tok) == "__" then getNameOfOpId (Id toks a b)
    else tokStr tok


-- isLogId :: Id -> Bool
-- isLogId i = (i == andId) 
--          || (i == orId) 
--          || (i == implId) 
--          || (i == eqvId) 
--          || (i == notId) 
--          || (i == defId) 
--          || (i == exEq) 
--          || (i == eqId) 


toPair :: GenVarDecl -> (Var,Type)
toPair (GenVarDecl (VarDecl var typ _ _)) = (var,typ)
toPair _ = error "[Comorphims.Haskell2IsabelleHOLCF] Not supported GenVarDecl"


binConst :: String -> IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binConst s t1 t2 = termAppl (termAppl (con s) t1) t2

termAppl :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
termAppl t1 t2 = t1 `App` t2


con :: String -> IsaSign.Term
con s = Const(s, dummyT)

conSome :: IsaSign.Term
conSome = con "Some"

conSomeT :: Typ -> IsaSign.Term
conSomeT t = Const("Some", t)

defOp :: IsaSign.Term
defOp = con "defOp"


conj :: String
conj = "op &"

disj :: String
disj = "op |"

impl :: String
impl = "op -->"

eqv :: String
eqv = "op <=>"

eq :: String
eq = "op ="

pairC :: String
pairC = "pair"

isaPair :: String
isaPair = "Pair"

some :: String
some = "Some"

-}
