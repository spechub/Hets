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

-- HasCASL
import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le as Le
import HasCASL.As as As
import HasCASL.Builtin
import HasCASL.Morphism

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

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


-- ============================ Signature ================================== --


transSignature :: Env
                   -> Maybe (IsaSign.Sign,[Named IsaSign.Sentence]) 
transSignature sign = 
  Just (IsaSign.emptySign {
    baseSig = "MainHC",
    -- translation of typeconstructors
    tsig = emptyTypeSig 
             { arities = Map.foldWithKey extractTypeName 
                                        Map.empty 
                                        (typeMap sign) },
    -- translation of operation declarations
    constTab = Map.foldWithKey insertOps 
                               Map.empty 
                               (assumps sign),
    -- translation of datatype declarations
    dataTypeTab = transDatatype (typeMap sign),
    showLemmas = True },
    [] ) 
   where 
    extractTypeName tId typeInfo m = 
        if isDatatypeDefn typeInfo then m
           else Map.insert (showIsa tId) [(isaTerm, [])] m
                -- translate the kind here!
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
transType (TypeName tId _ i)       = 
    if i == 0 then Type (showIsa tId) [] [] [] -- translate kind here!!
       else TFree (showIsa tId) []
transType (ProductType types _)       = foldl1 IsaSign.prodType 
                                               (map transType types)
transType (FunType type1 arr type2 _) = 
  case arr of
    PFunArr -> mkFunType (transType type1) (mkOptionType (transType type2))
    FunArr  -> mkFunType (transType type1) (transType type2)
    _       -> 
      error "[Comorphisms.HasCASL2IsabelleHOL] Not supported function type"
transType (TypeAppl type1 type2)      = 
    mkTypeAppl (transType type1) $ transType type2
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
  where mkDName ti ta = Type (showIsa ti) [] [] (map transTypeArg ta)

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
    Le.Formula t      -> Just (transTerm e t)
    DatatypeSen _     -> Nothing
    ProgEqSen _ _ _pe -> Nothing


transOpId :: Env -> UninstOpId -> TypeScheme -> String
transOpId sign op ts = 
  case (do ops <- Map.lookup op (assumps sign)
           if isSingle (opInfos ops) then return $ showIsa op
             else do i <- elemIndex ts (map opType (opInfos ops))
                     return $ showIsaI op (i+1)) of
    Just str -> str  
    Nothing  -> showIsa op

transTerm :: Env -> As.Term -> IsaSign.Term
transTerm _ (QualVar (VarDecl var typ _ _)) = 
  let tp  = transType typ 
      otp = mkFunType tp $ mkOptionType tp
  in  termAppl (conSomeT otp) (IsaSign.Free (transVar var) tp isaTerm)

transTerm sign (QualOp _ (InstOpId opId _ _) ts _)
  | opId == trueId  =  con "True"
  | opId == falseId = con "False"
  | otherwise       = termAppl conSome (con (transOpId sign opId ts))

transTerm sign (ApplTerm term1 term2 _) =
  transApplTerm term1
  where
   transApplTerm t =
     case t of
       QualOp Fun (InstOpId opId _ _) _ _ -> 
         if opId == whenElse then transWhenElse sign term2
           else transLog sign opId term1 term2 
       QualOp Pred _ _ _ -> termAppl (termAppl (con "pApp") 
                                      (transTerm sign term1)) 
                            (transTerm sign term2)
       QualOp Op _ typeScheme _ -> 
         if isPart typeScheme then mkApp "app"
           else mkApp "apt"
       ApplTerm t1 _ _ -> transApplTerm t1
       _               -> mkApp "app"
   mkApp s = termAppl (termAppl (con s) (transTerm sign term1)) 
             (transTerm sign term2)
   isPart (TypeScheme _ op _) = 
     case op of
       FunType _ PFunArr _ _ -> True
       FunType _ FunArr _ _  -> False
       _                     -> 
         error "[Comorphisms.HasCASL2IsabelleHOL] Wrong operation type"

transTerm sign (QuantifiedTerm quan varDecls phi' _) = 
  foldr (quantify quan) (transTerm sign phi') varDecls
  where
    quantify q gvd phi  = 
      case gvd of
        (GenVarDecl (VarDecl var typ _ _)) ->
          termAppl (con $ qname q) (Abs (con $ transVar var) 
                               (transType typ) phi NotCont)
        (GenTypeVarDecl (TypeArg _ _ _ _)) ->  phi
    qname Universal   = allS
    qname Existential = exS
    qname Unique      = ex1S

transTerm sign (TypedTerm t _ _ _) = transTerm sign t

transTerm sign (LambdaTerm pats part body _) =
  case part of
    Partial -> lambdaAbs transTerm
    Total   -> lambdaAbs transTotalLambda
  where 
   lambdaAbs f =
     if (null pats) then termAppl conSome 
                           (Abs (IsaSign.Free "dummyVar" noType isaTerm) 
                                     noType (f sign body) IsCont)
       else termAppl conSome (foldr (abstraction sign) 
                                 (f sign body)
                                 pats)

transTerm sign (LetTerm As.Let eqs body _) = 
  IsaSign.Let (map transPEq eqs) (transTerm sign body) IsCont
  where
    transPEq (ProgEq pat t _) = 
      (transPattern sign pat, transPattern sign t)


transTerm sign (TupleTerm terms _) =
  foldl1 (binConst pairC) (map (transTerm sign) terms)

transTerm sign (CaseTerm t pEqs _) = 
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
  | opId == notId  = termAppl notOp (transTerm sign t)
  | opId == defId  = termAppl defOp (transTerm sign t)
  | opId == exEq   = 
      binConst conj 
        (binConst conj 
          (binConst eq (transTerm sign t1) 
                       (transTerm sign t2))
          (termAppl defOp (transTerm sign t1)))
        (termAppl defOp (transTerm sign t2))
  | opId == eqId = binConst eq (transTerm sign t1)
                               (transTerm sign t2)
  | otherwise = termAppl (transTerm sign opTerm) (transTerm sign t)
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
          error "HasCASL2IsabelleHOL.abstraction"
    evalTupleType t = foldr1 IsaSign.prodType (map getType t)

{- translation of lambda patterns --> without constant:t 
    -> Some constant:t option -}
transPattern :: Env -> As.Term -> IsaSign.Term
transPattern _ (QualVar (VarDecl var typ _ _)) = 
  IsaSign.Free (transVar var) (transType typ) isaTerm
transPattern sign (TupleTerm terms _) = foldl1 (binConst isaPair) 
                                               (map (transPattern sign) terms)
transPattern _ (QualOp _ (InstOpId opId _ _) _ _) = con (showIsa opId)
transPattern sign (TypedTerm t _ _ _) = transPattern sign t
transPattern sign (ApplTerm t1 t2 _) = App (transPattern sign t1) (transPattern sign t2) IsCont
transPattern sign t = transTerm sign t

-- translation of bodies of total lambda abstractions
transTotalLambda :: Env -> As.Term -> IsaSign.Term
transTotalLambda _ (QualVar (VarDecl var typ _ _)) = 
  IsaSign.Free(transVar var) (transType typ) isaTerm
transTotalLambda sign t@(QualOp _ (InstOpId opId _ _) _ _) =
  if (opId == trueId) || (opId == falseId) then transTerm sign t
    else con (showIsa opId)
transTotalLambda sign (ApplTerm term1 term2 _) =
  termAppl (transTotalLambda sign term1) (transTotalLambda sign term2)
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
  where transCaseAltTotal (ProgEq pat trm _) = 
                (transPat sign pat, transTotalLambda sign trm)
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
transLetPat sign t@(QualVar (VarDecl _var _typ _ _)) = transPattern sign t
transLetPat sign t@(TupleTerm _terms _) = transPattern sign t
transLetPat sign t@(QualOp _ (InstOpId _opId _ _) _ _) = transPattern sign t
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

{- Annotation concerning Patterns:
     Following the HasCASL-Summary and the limits of this encoding
     patterns may take the form:
        QualVar, QualOp, ApplTerm, TupleTerm and TypedTerm 
-}

-- Input: List of case alternative one pattern per term
-- Functionality: Tests wheter pattern is a variable -> case alternative are
--                translated
arangeCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
arangeCaseAlts sign pEqs 
  | and (map patIsVar pEqs) = map (transCaseAlt sign) pEqs
  | otherwise               =  sortCaseAlts sign pEqs
  

-- Input: List of case alternatives, that patterns does consist of datatype constructors
--        (with arguments) or tupels
-- Functionality: Groups case alternatives by leading pattern-constructor
--                each pattern group is 'unfolded'
-- !! Von hier an hat man es nur mit EINER Art von leading constructor zu tun!!
sortCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
sortCaseAlts sign pEqs = 
  let consList
        | null pEqs = error "No case alternatives."
        | otherwise = getCons sign (getName (head pEqs))
      groupedByCons = Data.List.nub (map (groupCons pEqs) consList)
  in  map (flattenPattern sign) groupedByCons

-- Returns a list of the constructors of the used datatype
getCons :: Env -> TypeId -> [UninstOpId]
getCons sign tId = 
  extractIds (typeDefn (Map.find tId (typeMap sign)))
  where extractIds (DatatypeDefn (DataEntry _ _ _ _ altDefns)) =
          catMaybes (map stripConstruct altDefns)
        extractIds _ = error "HasCASL2Isabelle.extractIds"
        stripConstruct (Construct i _ _ _) = i

-- Extracts the type of the used datatype in case patterns
getName :: ProgEq -> TypeId
getName (ProgEq pat _ _) = (getTypeName pat)

getTypeName p =
   case p of
     QualVar (VarDecl _ typ _ _)       -> name typ
     QualOp _ _ (TypeScheme _ typ _) _ -> name typ
     TypedTerm _ _ typ _               -> name typ
     ApplTerm  t _ _                   -> getTypeName t
     TupleTerm ts _                    -> getTypeName (head ts)
     _                                 -> error "HasCASL2IsabelleHOL.getTypeName"
   where name tp = case tp of 
                     TypeName tyId _ 0       -> tyId
                     TypeAppl tp' _          -> name tp'
                     FunType _ _ tp' _       -> name tp'
                     ProductType (tp':tps) _ -> name tp'
                     _                       -> 
                       error "HasCASL2IsabelleHOL.name (of type)"


-- Input: Case alternatives and name of one constructor
-- Functionality: Filters case alternatives by constructor's name
groupCons :: [ProgEq] -> UninstOpId -> [ProgEq]
groupCons pEqs name = filter hasSameName pEqs
  where hasSameName (ProgEq pat _ _) = 
           hsn pat
        hsn pat =
          case pat of
            QualOp _ (InstOpId n _ _) _ _ -> n == name
            ApplTerm t1 _ _               -> hsn t1
            TypedTerm t _ _ _             -> hsn t
            TupleTerm _ _                 -> True
            _                             -> False



-- Input: List of case alternatives with same leading constructor
-- Functionality: Tests whether the constructor has no arguments, if so
--                translates case alternatives
--                if not

flattenPattern :: Env -> [ProgEq] -> (IsaSign.Term, IsaSign.Term)
flattenPattern sign pEqs
  | null pEqs         = error "Missing constructor alternative in case pattern."
  | isSingle pEqs     = (transCaseAlt sign) (head pEqs)
 -- at this stage there are patterns left which use 'ApplTerm' or 'TupleTerm'
 -- or the 'TypedTerm' variant of one of them
  | otherwise = let m = concentrate (matricize pEqs) sign
                in 
                    transCaseAlt sign (ProgEq (shrinkPat m) (term m) nullPos)

{- First of all a matrix is allocated (matriArg) with the arguments of a
 constructor resp.  of a tuple. They're binded with the term, that would
 be executed if the pattern matched.  Then the resulting list of
 matrices is grouped by the leading argument. (groupArgs) Afterwards -
 if a list of grouped arguments has more than one element - the last
 pattern argument (in the list 'patterns') is ...  -}

data CaseMatrix = CaseMatrix { patBrand :: PatBrand,
                               cons     :: Maybe As.Term,
                               args     :: [Pattern],
                               newArgs  :: [Pattern],
                               term     :: As.Term } deriving (Show)

data PatBrand = Appl | Tuple | QuOp | QuVar deriving (Eq, Show)

instance Eq CaseMatrix where
 (==) cmx cmx' = (patBrand cmx   == patBrand cmx') 
                && (args cmx     == args cmx')
                && (term cmx     == term cmx') 
                && (cons cmx     == cons cmx')
                && (newArgs cmx  == newArgs cmx')

-- Input: List with CaseMatrix of same leading constructor pattern
-- Functionality: First: Groups CMs so that these CMs are in one list
--                that only differ in their last argument
--                then: reduces list of every CMslist to one CM
--                if there's only one CM left -> 
--
concentrate :: [CaseMatrix] -> Env -> CaseMatrix
concentrate cmxs sign
  | isSingle cmsWithSubstitutedLastArg = head cmsWithSubstitutedLastArg
  | otherwise                          = concentrate cmsWithSubstitutedLastArg sign
  where cmll = Data.List.nub (map (groupByArgs cmxs) [0..(length cmxs-1)])
        cmsWithSubstitutedLastArg = map (redArgs sign) cmll


groupByArgs :: [CaseMatrix] -> Int -> [CaseMatrix]
groupByArgs cmxs i
  | and (map null (map args cmxs)) = cmxs
  | otherwise                      = (filter equalPat cmxs)
  where patE = init (args (cmxs !! i))
        equalPat cmx = isSingle (args cmx) || init (args cmx) == patE

-- Functionality: turns ProgEq into CaseMatrix
matricize :: [ProgEq] -> [CaseMatrix]
matricize =  map matriPEq


matriPEq :: ProgEq -> CaseMatrix
matriPEq (ProgEq pat altTerm _) = matriArg pat altTerm

matriArg :: Pattern -> As.Term -> CaseMatrix
matriArg pat cTerm =
  case pat of 
    ApplTerm t1 t2 _    -> let (c, p) = stripAppl t1 (Nothing, [])
                           in 
                             CaseMatrix { patBrand = Appl,
                                          cons     =  c,
                                          args     = p ++ [t2],
                                          newArgs  = [],
                                          term     = cTerm }
    TupleTerm ts _      -> CaseMatrix { patBrand = Tuple,
                                        cons     = Nothing,
                                        args     = ts,
                                        newArgs  = [],
                                        term     = cTerm }
    TypedTerm t _ _ _   -> matriArg t cTerm
    qv@(QualVar _)      -> CaseMatrix { patBrand = QuVar,
                                        cons     = Nothing,
                                        args     = [qv],
                                        newArgs  = [],
                                        term     = cTerm }
    qo@(QualOp _ _ _ _) -> CaseMatrix { patBrand = QuOp,
                                        cons     = Nothing,
                                        args     = [qo],
                                        newArgs  = [],
                                        term     = cTerm }
    _                   -> error "HasCASL2IsabelleHOL.matriArg"
-- Assumption: The innermost term of a case-pattern consisting of a ApplTerm
--             is a QualOp, that is a datatype constructor
  where stripAppl ct tp = 
          (case ct of
            TypedTerm (ApplTerm q@(QualOp _ _ _ _) t' _) _ _ _ -> (Just q, [t'] ++ snd tp)
            TypedTerm (ApplTerm (TypedTerm 
              q@(QualOp _ _ _ _) _ _ _) t' _) _ _ _ -> (Just q, [t'] ++ snd tp)
            TypedTerm (ApplTerm t' t'' _) _ _ _                -> 
              stripAppl t' (fst tp, [t''] ++ snd tp)
            ApplTerm q@(QualOp _ _ _ _) t' _ -> (Just q, [t'] ++ snd tp)
            ApplTerm (TypedTerm 
              q@(QualOp _ _ _ _) _ _ _) t' _ -> (Just q, [t'])
            ApplTerm t' t'' _                -> 
              stripAppl t' (fst tp, [t''] ++ snd tp)
--            TypedTerm t' _ _ _               -> stripAppl t' tp
            q@(QualOp _ _ _ _)               -> (Just q, snd tp)
            _                                -> (Nothing, [ct] ++ snd tp))


redArgs :: Env -> [CaseMatrix] -> CaseMatrix
redArgs sign caMas
  | and (map (testPatBrand Appl) caMas)  = redAppl caMas sign
  | and (map (testPatBrand Tuple) caMas) = redAppl caMas sign
  | isSingle caMas                       = head caMas
  | otherwise                            = head caMas
  where testPatBrand pb cm = pb == patBrand cm

-- Input: List of CMs thats leading constructor and arguments except the last one are equal
-- Functionality: Reduces n CMs to one with same last argument in pattern
redAppl :: [CaseMatrix] -> Env -> CaseMatrix
redAppl caMas sign
  | and (map null (map args caMas)) = head caMas
  | isSingle caMas                  = 
      hCaMas { args     = init (args hCaMas),
               newArgs  = (last (args hCaMas)):(newArgs hCaMas) }
  | and (map termIsVar lastArgs)        = substVar (head caMas)
  | otherwise                           = substTerm (head caMas)
   where terms = map term caMas
         hCaMas = head caMas
         lastArgs = map last (map args caMas)
         varName = "caseVar" ++ show (length (args (head caMas)))
         varId = (mkId [(mkSimpleId varName)])
         newVar = QualVar (VarDecl varId (TypeName varId MissingKind 1) Other [])
         newPEqs = (map newPE (zip lastArgs terms))
         newPEqs' = recArgs sign newPEqs
         substVar caMa 
           | null (args caMa)     = caMa
           | isSingle (args caMa) = 
               caMa { args    = [],
                      newArgs = last(args caMa) : (newArgs caMa) }
           | otherwise                =
               caMa { args    = init (args caMa),
                      newArgs = last(args caMa) : (newArgs caMa) }
         substTerm caMa
           | null (args caMa)     = caMa
           | isSingle (args caMa) =
               caMa { args    = [], 
                      newArgs = newVar : (newArgs caMa),
                      term    = CaseTerm newVar newPEqs' [] }
           | otherwise                =
               caMa { args    = init(args caMa), 
                      newArgs = newVar : (newArgs caMa),
                      term    = CaseTerm newVar newPEqs' [] }

recArgs :: Env -> [ProgEq] -> [ProgEq]
recArgs sign newPEqs 
  | isSingle groupedByCons 
      || null groupedByCons = []
  | otherwise               = doPEQ groupedByCons []
  where consList
          | null newPEqs = error "No case alternatives."
          | otherwise    = getCons sign (getName (head newPEqs))
        groupedByCons = map (groupCons newPEqs) consList
        doPEQ [] res = res
        doPEQ (g:gByCs) res
          | isSingle g = doPEQ gByCs (res ++ g)
          | otherwise  = doPEQ gByCs (res ++ [(toPEQ (testPEQs sign g))])
        toPEQ cmx = ProgEq (shrinkPat cmx) (term cmx) nullPos

testPEQs :: Env -> [ProgEq] -> CaseMatrix
testPEQs sign pEqs
  | null pEqs = error "HasCASL2IsabelleHOL.testPEQs"
  | otherwise = concentrate (matricize pEqs) sign

newPE (p, t) = ProgEq p t nullPos

newPEq cm = ProgEq (head (args cm)) (term cm) nullPos


shrinkPat :: CaseMatrix -> As.Term
shrinkPat caMa = 
  case patBrand caMa of
    Appl  -> case cons caMa of
               Just c ->  foldl mkApplT c ((args caMa) ++ (newArgs caMa))
               Nothing -> error "HasCASL2IsabelleHOL.shrinkPat"
    Tuple -> TupleTerm ((args caMa) ++ (newArgs caMa)) []
    QuOp  -> head (args caMa)
    _     -> head (newArgs caMa)
  where mkApplT t1 t2 = ApplTerm t1 t2 []


patIsVar :: ProgEq -> Bool
patIsVar (ProgEq pat _ _) = termIsVar pat

termIsVar :: As.Term -> Bool
termIsVar t = case t of
                QualVar _          -> True
                TypedTerm tr _ _ _ -> termIsVar tr
                TupleTerm ts _     -> and (map termIsVar ts)
                _                  -> False

patHasNoArg :: ProgEq -> Bool
patHasNoArg (ProgEq pat _ _) = termHasNoArg pat

termHasNoArg :: As.Term -> Bool
termHasNoArg t = case t of
                 QualOp _ _ _ _     -> True
                 TypedTerm tr _ _ _ -> termHasNoArg tr
                 _                  -> False

transCaseAlt :: Env -> ProgEq -> (IsaSign.Term, IsaSign.Term)
transCaseAlt sign (ProgEq pat trm _) = 
  (transPat sign pat, (transTerm sign trm))

transPat :: Env -> As.Term -> IsaSign.Term
transPat _ (QualVar (VarDecl var _ _ _)) = 
    IsaSign.Free (transVar var) noType isaTerm
transPat sign (ApplTerm term1 term2 _) = 
  termAppl (transPat sign term1) (transPat sign term2)
transPat sign (TypedTerm trm _ _ _) = transPat sign trm
transPat sign (TupleTerm terms _) =
  foldl1 (binConst isaPair) (map (transPat sign) terms)
transPat _ (QualOp _ (InstOpId i _ _) _ _) = con (showIsa i)
transPat _ _ =  error "HasCASL2IsabelleHOL.transPat"

showPEQ peqs = "PEQ-Liste: "++show (map spe peqs) ++"\n\n"
spe (ProgEq pat term _) = "PEQ Pattern: " ++ sT pat++"   "++"Term: "++sT term++"\n"
sT (QualVar (VarDecl v _ _ _)) = show v 
sT (QualOp _ (InstOpId i _ _) _ _) = show i
sT (ApplTerm t1 t2 _) = "ApplT ("++sT t1++") ("++sT t2++")"
sT (TupleTerm ts _) = "TupleT "++concat (map sT ts)
sT (TypedTerm t _ _ _) = "Typed "++sT t
sT (CaseTerm t peqs _) = "Case "++sT t++" "-- ++showPEQ peqs
sT t = show t


showCM cm = "MATRIX -+- Cons: PB: "++show (patBrand cm)++" Pats: "++concat (map sT (args cm))++" newArgs: "++concat (map sT (newArgs cm))++" term: "++sT (term cm)