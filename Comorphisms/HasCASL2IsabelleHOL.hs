{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from HasCASL to Isabelle-HOL.

-}

module Comorphisms.HasCASL2IsabelleHOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import Data.List
import Data.Maybe
import Common.AS_Annotation (Named(..))
import Debug.Trace

-- HasCASL
import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le as Le
import HasCASL.As as As
import HasCASL.Builtin
import HasCASL.Morphism

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaPrint

-- import Comorphisms.HC2I_Case
import Comorphisms.HC2I_Utils

-- | The identity of the comorphism
data HasCASL2IsabelleHOL = HasCASL2IsabelleHOL deriving (Show)

instance Language HasCASL2IsabelleHOL -- default definition is okay

instance Comorphism HasCASL2IsabelleHOL
               HasCASL HasCASL_Sublogics
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = HasCASL
    sourceSublogic _ = HasCASL_SL
                       { has_sub = False,   -- subsorting
                         has_part = True,   -- partiality
                         has_eq = True,     -- equality
                         has_pred = True,   -- predicates
                         has_ho = True,     -- higher order
                         has_type_classes = False,
                         has_polymorphism = True,
                         has_type_constructors = True,
                         which_logic = HOL
                       }
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_sign _ = transSignature
    -- map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign phi =
       case transSentence sign phi of
         Nothing   -> Nothing
         Just (ts) -> Just $ Sentence {senTerm = ts}
    -- map_symbol :: cid -> symbol1 -> Set symbol2


-- ================================== Signature ================================== --


transSignature :: Env
                   -> Maybe (IsaSign.Sign,[Named IsaSign.Sentence]) 
transSignature sign = 
  Just (IsaSign.Sign {
    baseSig = "MainHC",
    -- translation of typeconstructors
    tsig = emptyTypeSig 
             { tycons = Map.foldWithKey extractTypeName 
                                        Map.empty 
                                        (typeMap sign) },
    -- translation of operation declarations
    constTab = Map.foldWithKey insertOps 
                               Map.empty 
                               (assumps sign),
    -- translation of datatype declarations
    dataTypeTab = transDatatype (typeMap sign),
    syn = (),
    showLemmas = True },
    [] ) 
   where 
    extractTypeName typeId typeInfo m = if isDatatypeDefn typeInfo then m
                                          else Map.insert (showIsa typeId) 0 m
    isDatatypeDefn t = case typeDefn t of
                         DatatypeDefn _ -> True
                         _              -> False
    insertOps opName opInfs m = 
     let opIs = opInfos opInfs
     in if isSingle opIs then
            let transOp = transOpInfo (head opIs)
            in case transOp of 
                 Just op -> Map.insert (showIsa opName) op m
                 Nothing -> m
          else 
            let transOps = map transOpInfo opIs
            in  foldl (\ m1 (transOp,i) -> 
                           case transOp of
                             Just typ -> Map.insert (showIsaI opName i) 
                                                    typ m1
                             Nothing   -> m1)
                      m
                      (zip transOps [1..length transOps])


---------- translation of a type in an operation declaration ----------

transOpInfo :: OpInfo -> Maybe Typ
transOpInfo (OpInfo opT _ opDef) = 
  case opDef of
    NoOpDefn Pred   -> Just (transPredType opT)
    NoOpDefn _      -> Just (transOpType opT)
    ConstructData _ -> Nothing
    Definition _ _  -> Just (transOpType opT)
    _               -> 
      error ("[Comorphisms.HasCASL2IsabelleHOL] Not supported" 
                 ++ "operation declaration and/or definition")

-- operation
transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ op _) = transType op

-- predicate
transPredType :: TypeScheme -> Typ
transPredType  (TypeScheme _ pre _) = 
       case pre of
         FunType tp _ _ _ -> mkFunType (transType tp) boolType
         _                -> 
           error "[Comorphisms.HasCASL2IsabelleHOL] Wrong predicate type"

-- types composed of simple types
transType :: Type -> Typ
transType (TypeName typeId _ i)       = 
    if i == 0 then Type (showIsa typeId) [] []
       else TFree (showIsa typeId) []
transType (ProductType types _)       = foldl1 IsaSign.mkProductType 
                                               (map transType types)
transType (FunType type1 arr type2 _) = 
  case arr of
    PFunArr -> mkFunType (transType type1) (mkOptionType (transType type2))
    FunArr  -> mkFunType (transType type1) (transType type2)
    _       -> 
      error "[Comorphisms.HasCASL2IsabelleHOL] Not supported function type"
transType (TypeAppl type1 type2)      = 
  Type "typeAppl" [] ([transType type1] ++ [transType type2])
transType _ = error "[Comorphisms.HasCASL2IsabelleHOL] Not supported type"


---------- translation of a datatype declaration ----------

transDatatype :: TypeMap -> DataTypeTab
transDatatype tm = map transDataEntry (Map.fold extractDataypes [] tm)
  where extractDataypes ti des = case typeDefn ti of
                                   DatatypeDefn de -> des++[de]
                                   _               -> des

-- datatype with name (tyId) + args (tyArgs) and alternatives
transDataEntry :: DataEntry -> DataTypeTabEntry
transDataEntry (DataEntry _ tyId Le.Free tyArgs alts) = 
                         [((mkDName tyId tyArgs), (map mkAltDefn alts))]
  where mkDName ti ta = Type (showIsa ti) [] (map transTypeArg ta)

transDataEntry _ = 
  error "[Comorphisms.HasCASL2IsabelleHOL] Not supported datatype definition"

-- arguments of datatype's typeconstructor
transTypeArg :: TypeArg -> Typ
transTypeArg (TypeArg tyId _ _ _) = TFree (showIsa tyId) []


mkAltDefn :: AltDefn -> DataTypeAlt
mkAltDefn (Construct opId types Total _) = 
   let typs = map transType types
   in case opId of
        Just opI -> (showIsa opI, typs)
        Nothing  -> ("", typs)
mkAltDefn _ = 
  error ("[Comorphisms.HasCASL2IsabelleHOL] Not supported"
           ++ "alternative definition in (free) datatype")


------------------------------ Formulas ------------------------------

transVar :: Var -> String
transVar = showIsa


transSentence :: Env -> Le.Sentence -> Maybe IsaSign.Term
transSentence e s = case s of
    Le.Formula t      -> --trace ("TERM: "++show t++"\n\n" ++ "IsaTERM: "++ show  (transTerm e t)) 
          (Just (transTerm e t))
    DatatypeSen _     -> Nothing
    ProgEqSen _ _ _pe -> Nothing


transTerm :: Env -> As.Term -> IsaSign.Term
transTerm _ (QualVar (VarDecl var typ _ _)) = 
  let tp  = transType typ 
      otp = mkFunType tp $ mkOptionType tp
  in  App (conSomeT otp) (IsaSign.Free (transVar var) tp isaTerm) IsCont

transTerm sign (QualOp _ (InstOpId opId _ _) ts _)
  | opId == trueId  =  con "True"
  | opId == falseId = con "False"
  | otherwise       = App conSome (con (transOpId sign opId ts)) IsCont

transTerm sign (ApplTerm term1 term2 _) =
  transApplTerm term1
  where
   transApplTerm t =
     case t of
       QualOp Fun (InstOpId opId _ _) _ _ -> 
         if opId == whenElse then transWhenElse sign term2
           else transLog sign opId term1 term2 
       QualOp Pred _ _ _ -> App (App (con "pApp") (transTerm sign term1) 
                                 NotCont) (transTerm sign term2) NotCont
       QualOp Op _ typeScheme _ -> 
         if isPart typeScheme then mkApp "app"
           else mkApp "apt"
       ApplTerm t1 _ _ -> transApplTerm t1
       _               -> mkApp "app"
   mkApp s = App (App (con s) (transTerm sign term1) IsCont) 
                   (transTerm sign term2) IsCont
   isPart (TypeScheme _ op _) = 
     case op of
       FunType _ PFunArr _ _ -> True
       FunType _ FunArr _ _  -> False
       _                     -> 
         error "[Comorphisms.HasCASL2IsabelleHOL] Wrong operation type"

transTerm sign (QuantifiedTerm quan varDecls phi _) = 
  foldr (quantify quan) (transTerm sign phi) varDecls
  where
    quantify q gvd phi  = 
      case gvd of
        (GenVarDecl (VarDecl var typ _ _)) ->
          App (con $ qname q) (Abs (con $ transVar var) 
                               (transType typ) phi NotCont) NotCont
        (GenTypeVarDecl (TypeArg _ _ _ _)) ->  phi
    qname Universal   = "All"
    qname Existential = "Ex"
    qname Unique      = "Ex1"

transTerm sign (TypedTerm t _ _ _) = transTerm sign t

transTerm sign (LambdaTerm pats part body _) =
  case part of
    Partial -> lambdaAbs transTerm
    Total   -> lambdaAbs transTotalLambda
  where 
   lambdaAbs f =
     if (null pats) then App conSome 
                           (Abs (IsaSign.Free "dummyVar" noType isaTerm) 
                                     noType (f sign body) IsCont) IsCont
       else App conSome (foldr (abstraction sign) 
                                 (f sign body)
                                 pats) IsCont

transTerm sign (LetTerm As.Let eqs body _) = 
  IsaSign.Let (map (transPEq sign) eqs) (transTerm sign body) IsCont
  where
    transPEq sign (ProgEq pat t _) = 
      (transPattern sign pat, transPattern sign t)
--  transTerm sign (foldr let2lambda body eqs)

transTerm sign (TupleTerm terms _) =
  foldl1 (binConst pairC) (map (transTerm sign) terms)

transTerm sign (CaseTerm t pEqs _) = 
--  trace ("pEqs " ++ show pEqs ++ "\n")
  let alts = arangeCaseAlts sign pEqs
  in
    case t of
      QualVar (VarDecl decl _ _ _) -> 
        Case (IsaSign.Free (transVar decl) noType isaTerm) alts IsCont
      _                            -> 
        Case (transTerm sign t)
              ((con "None", con "None"):
               [(App conSome (IsaSign.Free "caseVar" noType isaTerm) IsCont,
               Case (IsaSign.Free "caseVar" noType isaTerm) alts IsCont)])
              IsCont

transTerm _ _ = 
  error "[Comorphisms.HasCASL2IsabelleHOL] Not supported (abstract) syntax."


-- translation formulas with logical connectives
transLog :: Env -> Id -> As.Term -> As.Term -> IsaSign.Term
transLog sign opId opTerm t
  | opId == andId  = foldl1 (binConst conj) 
                            (map (transTerm sign) ts)
  | opId == orId   = foldl1 (binConst disj) 
                            (map (transTerm sign) ts)
  | opId == implId = binConst impl (transTerm sign t1)
                                   (transTerm sign t2)
  | opId == eqvId  = binConst eqv (transTerm sign t1)
                                  (transTerm sign t2)
  | opId == notId  = App (con "Not") (transTerm sign t) NotCont
  | opId == defId  = App defOp (transTerm sign t) NotCont
  | opId == exEq   = 
      binConst conj 
        (binConst conj 
          (binConst eq (transTerm sign t1) 
                       (transTerm sign t2))
          (App defOp (transTerm sign t1) NotCont))
        (App defOp (transTerm sign t2) NotCont)
  | opId == eqId = binConst eq (transTerm sign t1)
                               (transTerm sign t2)
  | otherwise = App (transTerm sign opTerm) (transTerm sign t) IsCont
      where ts = getTerms t
            t1 = head ts
            t2 = last ts
            getTerms (TupleTerm terms _) = terms
            getTerms _ = 
              error ("[Comorphisms.HasCASL2IsabelleHOL] Incorrect"
                           ++ "formula coding in abstract syntax")


----------------- translation of lambda-things -----------------

-- form Abs(...)
abstraction :: Env -> As.Term -> IsaSign.Term -> IsaSign.Term
abstraction sign pat body = 
    Abs (transPattern sign pat) (getType pat) body IsCont where
    getType t =
      case t of
        QualVar (VarDecl _ typ _ _) ->  transType typ
        TypedTerm _ _ typ _         -> transType typ
        TupleTerm terms _           -> evalTupleType terms
        _                           -> 
          error "[Comorphisms.HasCASL2IsabelleHOL] Illegal pattern in lambda abstraction"
    evalTupleType t = foldr1 IsaSign.mkProductType (map getType t)

-- translation of lambda patterns --> without constant:t -> Some constant:t option
transPattern :: Env -> As.Term -> IsaSign.Term
transPattern _ (QualVar (VarDecl var typ _ _)) = 
  IsaSign.Free (transVar var) (transType typ) isaTerm
transPattern sign (TupleTerm terms _) = foldl1 (binConst isaPair) 
                                               (map (transPattern sign) terms)
transPattern _ (QualOp _ (InstOpId opId _ _) _ _) = con (showIsa opId)
transPattern sign t = transTerm sign t

-- translation of bodies of total lambda abstractions
transTotalLambda :: Env -> As.Term -> IsaSign.Term
transTotalLambda _ (QualVar (VarDecl var typ _ _)) = 
  IsaSign.Free(transVar var) (transType typ) isaTerm
transTotalLambda sign t@(QualOp _ (InstOpId opId _ _) _ _) =
  if (opId == trueId) || (opId == falseId) then transTerm sign t
    else con (showIsa opId)
transTotalLambda sign (ApplTerm term1 term2 _) =
  App (transTotalLambda sign term1) (transTotalLambda sign term2) IsCont
transTotalLambda sign (TypedTerm t _ _ _) = transTotalLambda sign t
transTotalLambda sign (LambdaTerm pats part body _) =
  case part of
    Partial -> lambdaAbs transTerm
    Total   -> lambdaAbs transTotalLambda
  where 
    lambdaAbs f =
      if (null pats) then Abs(IsaSign.Free "dummyVar" noType isaTerm) 
                              noType (f sign body) IsCont
        else  (foldr (abstraction sign) 
                     (f sign body)
                     pats)
transTotalLambda sign (TupleTerm terms _) =
  foldl1 (binConst isaPair) (map (transTotalLambda sign) terms)
transTotalLambda sign (CaseTerm t pEqs _) = 
  Case (transTotalLambda sign t) (map transCaseAltTotal pEqs) IsCont
  where transCaseAltTotal (ProgEq pat t _) = 
                (transPat sign pat, transTotalLambda sign t)
transTotalLambda sign t = transTerm sign t


transWhenElse :: Env -> As.Term -> IsaSign.Term
transWhenElse sign t =
    case t of
      TupleTerm terms _ -> 
        let ts = (map (transTerm sign) terms)
        in
           if (length ts) == 3 
              then If (head $ tail ts) (head  ts) (last ts) NotCont
              else error 
           "[Comorphisms.HasCASL2IsabelleHOL] Wrong when-else definition"
      _                 -> 
        error "[Comorphisms.HasCASL2IsabelleHOL] Wrong when-else definition"



let2lambda :: ProgEq -> As.Term -> As.Term
let2lambda (ProgEq pat t _) body = 
  ApplTerm (LambdaTerm [pat] Partial body [nullPos]) t [nullPos]


transLetPat :: Env -> As.Term -> IsaSign.Term
transLetPat sign t@(QualVar (VarDecl var typ _ _)) = transPattern sign t
transLetPat sign t@(TupleTerm terms _) = transPattern sign t
transLetPat sign t@(QualOp _ (InstOpId opId _ _) _ _) = transPattern sign t
--transLetPat sign (ApplTerm t1 t2) =
transLetPat sign t = transTerm sign t



{- todo
nested case patterns:
1. check if set of patterns is
1a. one pattern consisting of a variable => we are done
1b. set of constructor patterns 
    1b1. sort patterns according to leading constructor
    1b2. for each group of patterns with the same leading constructor
         1b2a. for each argument position, call 1. recursively

-}

-- Pattern: Following the HasCASL-Summary and the limits of this encoding
--          patterns may take the form
--          QualVar, QualOp, ApplTerm, TupleTerm and TypedTerm

arangeCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
arangeCaseAlts sign pEqs = 
--  trace ("peqs: "++show pEqs++"\n") 
  (if and (map patIsVar pEqs) then map (transCaseAlt sign) pEqs
    else sortCaseAlts sign pEqs)
  


sortCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
sortCaseAlts sign pEqs = 
  let consList =  getCons sign (getName (head pEqs))
      groupedConsInLists = map (groupCons pEqs) consList
  in
    concat (map (unfoldCons sign) groupedConsInLists)

-- Returns a list of the constructors of the used datatype
getCons :: Env -> TypeId -> [UninstOpId]
getCons sign tId = 
  extractIds (typeDefn (Map.find tId (typeMap sign)))
  where extractIds (DatatypeDefn (DataEntry _ _ _ _ altDefns)) =
          catMaybes (map stripConstruct altDefns)
        stripConstruct (Construct i _ _ _) = i


-- Extracts the type of the used datatype in case patterns
getName :: ProgEq -> TypeId
getName (ProgEq pat _ _) = 
--  trace ("gtn: "++show pat++"\n") 
 (getTypeName pat)
  where getTypeName p = case p of
                          QualVar (VarDecl _ typ _ _) -> name typ
                          QualOp _ _ (TypeScheme _ typ _) _ -> name typ
                          TypedTerm _ _ typ _ -> name typ
                          ApplTerm  t _ _ -> getTypeName t
                          TupleTerm ts _ -> getTypeName (head ts)
                          _ -> error "[Comorphisms.HasCASL2IsabelleHOL] Not allowed case pattern"
        name tp = --trace ("name: "++show tp++"\n") 
         (case tp of 
                   TypeName tyId _ 0 -> tyId
                   TypeAppl tp' _      -> name tp'
                   FunType tp' _ _ _  -> name tp'
                   -- ProductType
                   _                -> 
                      error "[Comorphims.HasCASL2IsabelleHOL] lllNot supported type")

groupCons :: [ProgEq] -> UninstOpId -> [ProgEq]
groupCons pEqs name = filter hasSameName pEqs
  where hasSameName (ProgEq pat _ _) = 
           hsn pat
        hsn pat =
          case pat of
            QualOp _ (InstOpId n _ _) _ _ -> n == name
            ApplTerm t1 _ _               -> hsn t1
            TypedTerm t _ _ _             -> hsn t
            TupleTerm ts _                -> hsn (head ts)
            _                             -> False



unfoldCons :: Env -> [ProgEq] -> [(IsaSign.Term, IsaSign.Term)]
unfoldCons sign pEqs =
--  trace ("unfold: "++show pEqs++"\n") 
  (if and (map patHasNoArg pEqs)
    then map (transCaseAlt sign) pEqs
 -- at this stage there are patterns left which use 'ApplTerm' or 'TupleTerm'
 -- or the 'TypedTerm' variant of one of them
      else matricize sign pEqs)


-- First of all a matrix is engaged (matriArg) with the arguments of a constructor resp.
-- of a tuple. They're bind with the term, that would be executed if the pattern
-- matched.
-- Then the resulting list of matrices is grouped by the leading argument. (groupArgs)
-- Afterwards - if a list of grouped arguments has more than one element - the last
-- pattern argument (in the list 'patterns') is ...

data PatBrand = Appl | Tuple | QuOp | QuVar deriving (Eq, Show)

data CaseMatrix = CaseMatrix { patBrand :: PatBrand,
                               patterns :: [Pattern],
                               term     :: As.Term,
                               cons     :: Maybe As.Term } deriving (Show)

instance Eq CaseMatrix where
 (==) cm1 cm2 = (patBrand cm1 == patBrand cm2) && (patterns cm1 == patterns cm2)
                  && (term cm1 == term cm2) && (cons cm1 == cons cm2)


matricize :: Env -> [ProgEq] -> [(IsaSign.Term, IsaSign.Term)]
matricize sign pEqs = 
  let caseMatrices = map matriPEq pEqs
      m = rm caseMatrices
  in
    [transCaseAlt sign (ProgEq (head (patterns m)) (term m) nullPos)]

rm :: [CaseMatrix] -> CaseMatrix
rm caseMatrices = 
  let cm = --trace ("b4group: "++show caseMatrices ++"\n") 
         (Data.List.nub (map (groupArgs caseMatrices) [0..(length caseMatrices)-1]))
  in
--   trace ("cm: "++show cm++"\n") 
    (reduce cm)
  
reduce :: [[CaseMatrix]] -> CaseMatrix
reduce listOfGroupedCMs = 
  let fstCMs = --trace ("cms "++show listOfGroupedCMs++"\n\n"++"redArgs "++show (map redArgs listOfGroupedCMs)++"\n") 
        (map redArgs listOfGroupedCMs)
  in
    if isSingle fstCMs then shrinkPat (head fstCMs) -- pattern zusammen fassen
      else if or (map isSinglePat fstCMs) then redArgs fstCMs
             else rm (map cutLastArg fstCMs)
  where isSinglePat cm = isSingle (patterns cm)
        cutLastArg cm = --trace ("cla"++show cm++"\n") 
           cm { patterns = init (patterns cm) }

matricizeArgs :: [Pattern] -> [As.Term] -> [CaseMatrix]
matricizeArgs pats cTerms = 
  let caseMatrices = --trace ("ma: "++show (map matriArgTuple (zip pats cTerms))++"\n") 
              (map matriArgTuple (zip pats cTerms))
      grouped = map (groupArgs caseMatrices) [0..(length caseMatrices)-1]
  in
--    trace (show (nub grouped)++"\n") 
        (map redArgs (nub grouped))
--     rm caseMatrices
  where matriArgTuple (p, t) = matriArg p t

groupArgs :: [CaseMatrix] -> Int -> [CaseMatrix]
groupArgs caMas i = 
  --trace ("i: "++show i++"\n"++"cm1: "++show (caMas !! i)++"\n") 
 (filter equalPat caMas)
  where patE = init (patterns (caMas !! i))
        pb = patBrand (caMas !! i)
        pe = patterns (caMas !! i)
        equalPat caMa = 
--         if (pb == Appl && (patBrand caMa) == Appl) || (pb == Tuple && (patBrand caMa) == Tuple) then 
--           trace ("ga: "++show (init (patterns caMa))++"\n") 
--                trace "equalPat" 
                  ((init (patterns caMa) == patE) && (cons (caMas !! i) == cons caMa))
--             else --trace ("gaE: "++show (patterns caMa)++"\n") 
--                 (patterns caMa == pe)
           
-- Maybe: have to write Eq instance for Terms resp. Patterns


matriPEq :: ProgEq -> CaseMatrix
matriPEq (ProgEq pat cTerm _) = matriArg pat cTerm

matriArg :: Pattern -> As.Term -> CaseMatrix
matriArg pat cTerm =
-- trace ("matriArg: " ++ show pat ++ "\n" ) 
  (case pat of 
    ApplTerm t1 t2 _   -> let (c, p) = stripAppl t1 (Nothing, [])
                          in 
                            CaseMatrix { patBrand = Appl,
                                         patterns = p ++ [t2],
                                         term = cTerm,
                                         cons =  c }
    TupleTerm ts _     -> CaseMatrix { patBrand = Tuple,
                                       patterns = ts,
                                       term = cTerm,
                                       cons = Nothing }
    TypedTerm t _ _ _  -> matriArg t cTerm
    qv@(QualVar _)     -> CaseMatrix { patBrand = QuVar,
                                       patterns = [qv],
                                       term = cTerm,
                                       cons = Nothing }
    qo@(QualOp _ _ _ _) -> CaseMatrix { patBrand = QuOp,
                                       patterns = [qo],
                                       term = cTerm,
                                       cons = Nothing })
-- Assumption: The innermost term of a case-pattern consisting of a ApplTerm
--             is a QualOp, that is a datatype constructor
  where stripAppl ct tp = 
--          trace ("stripAppl: " ++ show ct ++ "\n") 
         (case ct of
            ApplTerm qOp@(QualOp _ _ _ _) t' _                    -> (Just qOp, [t'] ++ snd tp)
            ApplTerm tQOp@(TypedTerm (QualOp _ _ _ _) _ _ _) t' _ -> (Just tQOp, [t'])
            ApplTerm t' t'' _                                     -> stripAppl t' (fst tp, [t''] ++ snd tp)
            qOp@(QualOp _ _ _ _)                                  -> (Just qOp, snd tp)
            _                                                     -> (Nothing, [ct] ++ snd tp))


redArgs :: [CaseMatrix] -> CaseMatrix
redArgs caMas
  | or (map (testPatBrand Appl) caMas)  = --trace ("appl "++show (redAppl caMas)++"\n") 
                (redAppl caMas)
  | or (map (testPatBrand Tuple) caMas) = head caMas
  | and (map (testPatBrand QuOp) caMas) = --trace "quop\n" 
               (redQuOp caMas)
  | otherwise                           = --trace "other\n" 
             shrinkPat (head caMas)
  where testPatBrand pb cm = pb == patBrand cm

redQuOp :: [CaseMatrix] -> CaseMatrix
redQuOp caMas =
  let terms = map term caMas
      hCaMas = head caMas
      varName = "caseVar" ++ show (length caMas)
      varId = (mkId [(mkSimpleId varName)])
      newVar = QualVar (VarDecl varId (TypeName varId MissingKind 1) Other [])
      newPEqs = map newPEq (map shrinkPat caMas)
  in
--    trace ("newPeqs: "++show newPEqs++"\n") 
    (if isSingle caMas then head (map shrinkPat caMas)
      else shrinkPat hCaMas { patterns = [newVar],
                              term = CaseTerm newVar newPEqs [] })

redAppl :: [CaseMatrix] -> CaseMatrix
redAppl caMas = 
  let terms = map term caMas
      hCaMas = head caMas
      lastArgs = map last (map patterns caMas)
--      laMas = --trace ("la "++show lastArgs++"\n"++"ma "++show (matricizeArgs lastArgs terms)++"\n") 
--              (matricizeArgs lastArgs terms)
--      shrinkedMas = map shrinkPat laMas
      varName = "caseVar" ++ show (length caMas)
      varId = (mkId [(mkSimpleId varName)])
      newVar = QualVar (VarDecl varId (TypeName varId MissingKind 1) Other [])
      newPEqs = --trace ("newPEqs: "++show lastArgs++"\n") 
              (map newPE (zip lastArgs terms)) --shrinkedMas
   in
    if isSingle caMas then shrinkPat (head caMas)
     else
      shrinkPat (hCaMas { patterns = init (patterns hCaMas) ++ [newVar],
                          term = CaseTerm newVar newPEqs [] })

newPE (p, t) = ProgEq p t nullPos
newPEq cm = ProgEq (head (patterns cm)) (term cm) nullPos


shrinkPat :: CaseMatrix -> CaseMatrix
shrinkPat caMa = 
--  trace ("shrinkPat: " ++ show caMa ++ "\n") 
  (case patBrand caMa of
    Appl  -> case cons caMa of
               Just c -> caMa { patBrand = QuOp,
                                patterns = [foldl mkApplT c (patterns caMa)]
                                 }
               Nothing -> error "[Comorphims.HasCASL2IsabelleHOL]: Error in case analysis."
--    Tuple ->
    _     -> caMa)
  where mkApplT t1 t2 = ApplTerm t1 t2 []


patIsVar :: ProgEq -> Bool
patIsVar (ProgEq pat _ _) = termIsVar pat

termIsVar :: As.Term -> Bool
termIsVar t = case t of
                QualVar _         -> True
                TypedTerm t _ _ _ -> termIsVar t
                TupleTerm ts _    -> and (map termIsVar ts)
                _                 -> False

patHasNoArg :: ProgEq -> Bool
patHasNoArg (ProgEq pat _ _) = termHasNoArg pat

termHasNoArg :: As.Term -> Bool
termHasNoArg t = case t of
                 QualOp _ _ _ _    -> True
                 TypedTerm t _ _ _ -> termHasNoArg t
                 _                 -> False

{-


substArg :: Env -> [ProgEq] -> [(IsaSign.Term, IsaSign.Term)]
substArg sign pEqs =
  let frontCons = transPat sign (getFrontCons pEqs)
      varName = "caseVar" ++ show (length pEqs)
      newPat = frontCons `App` IsaSign.Free(varName, noType)
      varId = (mkId [(mkSimpleId varName)])
      newVar = QualVar (VarDecl varId (TypeName varId MissingKind 1) Other [])
      newTerm = transTerm sign (CaseTerm newVar newPEqs [])
      newPEqs = map getNewPEqs pEqs
  in
     [(newPat, newTerm)]
  where getFrontCons ((ProgEq pat _ _):_) = 
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

-- transCaseEx :: Env -> As.Term -> IsaSign.Term
-- transCaseEx sign term =
--   case term of
--     QualVar (VarDecl decl _ _ _) -> IsaSign.Free(transVar decl, noType)
--     _                            -> transTerm sign term
-}
transCaseAlt :: Env -> ProgEq -> (IsaSign.Term, IsaSign.Term)
transCaseAlt sign (ProgEq pat term _) = 
  (transPat sign pat, --trace ("term: "++show term++"\n") 
                 (transTerm sign term))
   --Abs (transTerm sign pat, noType, transTerm sign term)

transPat :: Env -> As.Term -> IsaSign.Term
transPat _ (QualVar (VarDecl var _ _ _)) = 
    IsaSign.Free (transVar var) noType isaTerm
transPat sign (ApplTerm term1 term2 _) = 
  App (transPat sign term1) (transPat sign term2) IsCont
transPat sign (TypedTerm term _ _ _) = transPat sign term
-- transPat sign (LambdaTerm pats Partial body _) =
--   if (null pats) then Abs(IsaSign.Free("dummyVar",noType), 
--                                         noType, 
--                                         (transPat sign body))
--      else foldr (abstraction sign) 
--                 (transPat sign body)
--                 pats
-- transPat sign (LetTerm Let eqs body _) = 
--   transPat sign (foldr let2lambda body eqs)
transPat sign (TupleTerm terms _) =
  foldl1 (binConst isaPair) (map (transPat sign) terms)
transPat _ (QualOp _ (InstOpId i _ _) _ _) = con (showIsa i)
transPat _ _ =  error "[Comorphims.HasCASL2IsabelleHOL] Not supported (abstract) syntax."
