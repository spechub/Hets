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

module Comorphisms.HasCASL2IsabelleHOLCF where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import Data.List
import Data.Maybe
import Common.AS_Annotation (Named)
import Debug.Trace

-- HasCASL
import Haskell.Hatchet.HsSyn
import Haskell.Hatchet.MultiModuleBasics (ModuleInfo,
                                          emptyModuleInfo,
					  joinModuleInfo)
import Haskell.Hatchet.AnnotatedHsSyn    (AHsDecl)

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaPrint

-- | The identity of the comorphism
data Haskell2IsabelleHOLCF = Haskell2IsabelleHOLCF deriving (Show)

instance Language Haskell2IsabelleHOLCF -- default definition is okay

{-
instance Comorphism Haskell2IsabelleHOLCF
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
                         has_polymorphism = False,
                         has_type_constructors = False,
                         which_logic = HOL
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

-- data Sign = Sign { baseSig :: String, -- like Pure, HOL etc.
--                    tsig :: TypeSig,
--                    constTab :: Map.Map String Typ,
--                    syn :: Syntax
--                  }


transSignature :: ModuleInfo
                   -> Result(IsaSign.Sign,[Named IsaSign.Sentence]) 
-- see Common/Result.hs

-- needs to be done! Below, just the HasCASL code!!!

transSignature sign = 
  Just(IsaSign.Sign{
    baseSig = "MainHC",
    tsig = emptyTypeSig 
            {tycons = Map.foldWithKey extractTypeName 
                                      Map.empty 
                                      (typeMap sign)},
    constTab = Map.foldWithKey insertOps 
                               Map.empty 
                               (assumps sign),
    dataTypeTab = transDatatype (typeMap sign),
    syn = (),
    showLemmas = False },
    [] )  -- for now, no sentences
   where 
    extractTypeName typeId typeInfo m = if isDatatypeDefn typeInfo then m
                                         else Map.insert (showIsa typeId) 0 m
    isDatatypeDefn t = case typeDefn t of
                  DatatypeDefn _ -> True
                  _              -> False
    insertOps opName opInfs m = 
     let opIs = opInfos opInfs
     in if (length opIs) == 1 then
          let transOp = transOpInfo (head opIs)
          in case transOp of 
               Just op -> Map.insert (showIsa opName) op m
               Nothing -> m
          else 
            let transOps = map transOpInfo opIs
            in  foldl (\m1 (transOp,i) -> 
                           case transOp of
                             Just typ -> Map.insert (showIsaI opName i) 
                                                     typ m1
                             Nothing   -> m1)
                       m
                       (zip transOps [1..length transOps])

 
transOpInfo :: OpInfo -> Maybe Typ
transOpInfo (OpInfo opT _ opDef) = 
  case opDef of
    NoOpDefn Pred   -> Just (transPredType opT)
    NoOpDefn _      -> Just (transOpType opT)
    ConstructData _ -> Nothing
    _               -> error "[Comorphims.Haskell2IsabelleHOLCF] Not supported operation declaration and/or definition"


transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ op _) = transType op


transPredType :: TypeScheme -> Typ
transPredType  (TypeScheme _ pre _) = 
       case pre of
         FunType tp _ _ _ -> (transType tp) --> boolType
         _                -> 
           error "[Comorphims.Haskell2IsabelleHOLCF] Wrong predicate type"

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
