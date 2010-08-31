{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  old translation that is only better for case terms
Copyright   :  (c) Sonja Groening, C. Maeder, Uni Bremen 2003-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

This embedding comorphism from HasCASL to Isabelle-HOL is an old
version that can be deleted as soon as case terms are implemented elsewhere
-}

module Comorphisms.HasCASL2IsabelleHOL where

import Logic.Logic as Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le as Le
import HasCASL.As as As
import HasCASL.AsUtils
import HasCASL.Builtin

import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.AS_Annotation

import Data.List (elemIndex)
import Data.Maybe (catMaybes)

-- | The identity of the comorphism
data HasCASL2IsabelleHOL = HasCASL2IsabelleHOL deriving Show

instance Language HasCASL2IsabelleHOL where
  language_name HasCASL2IsabelleHOL = "HasCASL2IsabelleDeprecated"

instance Comorphism HasCASL2IsabelleHOL
               HasCASL Sublogic
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign
               IsabelleMorphism () () ()  where
    sourceLogic HasCASL2IsabelleHOL = HasCASL
    sourceSublogic HasCASL2IsabelleHOL = sublogic_min noSubtypes noClasses
    targetLogic HasCASL2IsabelleHOL = Isabelle
    mapSublogic cid sl = if sl `isSubElem` sourceSublogic cid
                       then Just () else Nothing
    map_theory HasCASL2IsabelleHOL = mkTheoryMapping transSignature
                   (map_sentence HasCASL2IsabelleHOL)
    map_morphism = mapDefaultMorphism
    map_sentence HasCASL2IsabelleHOL sign phi =
       case transSentence sign phi of
         Nothing   -> warning (mkSen true)
                           "translation of sentence not implemented" nullRange
         Just (ts) -> return $ mkSen ts
    isInclusionComorphism HasCASL2IsabelleHOL = True

-- * Signature
baseSign :: BaseSig
baseSign = MainHC_thy

transSignature :: Env -> Result (IsaSign.Sign,[Named IsaSign.Sentence])
transSignature sign =
  return (IsaSign.emptySign {
    baseSig = baseSign,
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
    domainTab = transDatatype (typeMap sign),
    showLemmas = True },
    [] )
   where
    extractTypeName tyId typeInfo m =
        if isDatatypeDefn typeInfo then m
           else Map.insert (showIsaTypeT tyId baseSign) [(isaTerm, [])] m
                -- translate the kind here!
    isDatatypeDefn t = case typeDefn t of
                         DatatypeDefn _ -> True
                         _              -> False
    insertOps name ops m =
          if isSingleton ops then
            let transOp = transOpInfo (Set.findMin ops)
            in case transOp of
                 Just op ->
                     Map.insert (mkVName $ showIsaConstT name baseSign) op m
                 Nothing -> m
          else
            let transOps = map transOpInfo $ Set.toList ops
            in  foldl (\ m' (transOp,i) ->
                           case transOp of
                             Just ty -> Map.insert
                                 (mkVName $ showIsaConstIT name i baseSign)
                                 ty m'
                             Nothing   -> m')
                      m $ number transOps

-- * translation of a type in an operation declaration

-- extract type from OpInfo
-- omit datatype constructors
transOpInfo :: OpInfo -> Maybe Typ
transOpInfo (OpInfo t _ opDef) =
  case opDef of
    ConstructData _ -> Nothing
    _  -> Just (transOpType t)

-- operation type
transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ op _) = transType op

-- types
transType :: Type -> Typ
transType t = case getTypeAppl t of
   (TypeName tid _ n, tyArgs) -> let num = length tyArgs in
      if n == 0 then
          if tid == unitTypeId && null tyArgs then boolType
          else if tid == lazyTypeId && num == 1 then
             transType $ head tyArgs
          else if isArrow tid && num == 2 then
             let [t1, t2] = tyArgs
                 tr = transType t2
             in mkFunType (transType t1) $
                    if isPartialArrow tid && not (isPredType t)
                        then mkOptionType tr else tr
          else if isProductId tid && num > 1 then
             foldl1 prodType $ map transType tyArgs
          else Type (showIsaTypeT tid baseSign) [] $ map transType tyArgs
       else TFree (showIsaTypeT tid baseSign) []
            -- type arguments are not allowed here!
   _ -> error $ "transType " ++ showDoc t "\n" ++ show t

-- * translation of a datatype declaration

transDatatype :: TypeMap -> DomainTab
transDatatype tm = map transDataEntry (Map.fold extractDataypes [] tm)
  where extractDataypes ti des = case typeDefn ti of
                                   DatatypeDefn de -> des++[de]
                                   _               -> des

-- datatype with name (tyId) + args (tyArgs) and alternatives
transDataEntry :: DataEntry -> [DomainEntry]
transDataEntry (DataEntry _ tyId Le.Free tyArgs _ alts) =
    [(transDName tyId tyArgs, map transAltDefn $ Set.toList alts)]
  where transDName ti ta = Type (showIsaTypeT ti baseSign) []
                           $ map transTypeArg ta
transDataEntry _ = error "HasCASL2IsabelleHOL.transDataEntry"

-- arguments of datatype's typeconstructor
transTypeArg :: TypeArg -> Typ
transTypeArg ta = TFree (showIsaTypeT (getTypeVar ta) baseSign) []

-- datatype alternatives/constructors
transAltDefn :: AltDefn -> (VName, [Typ])
transAltDefn (Construct opId ts Total _) =
   let ts' = map transType ts
   in case opId of
        Just opId' -> (mkVName $ showIsaConstT opId' baseSign, ts')
        Nothing  -> (mkVName "", ts')
transAltDefn _ = error "HasCASL2IsabelleHOL.transAltDefn"

-- * Formulas

-- simple variables
transVar :: Id -> VName
transVar v = mkVName $ showIsaConstT v baseSign

transSentence :: Env -> Le.Sentence -> Maybe IsaSign.Term
transSentence sign s = case s of
    Le.Formula t      -> Just (transTerm sign t)
    DatatypeSen _     -> Nothing
    ProgEqSen _ _ _pe -> Nothing

-- disambiguate operation names
transOpId :: Env -> Id -> TypeScheme -> String
transOpId sign op ts =
  case (do ops <- Map.lookup op (assumps sign)
           if isSingleton ops then return $ showIsaConstT op baseSign
             else do i <- elemIndex ts $ map opType $ Set.toList ops
                     return $ showIsaConstIT op (i+1) baseSign) of
    Just str -> str
    Nothing  -> showIsaConstT op baseSign

transProgEq :: Env -> ProgEq -> (IsaSign.Term, IsaSign.Term)
transProgEq sign (ProgEq pat t _) =
      (transPattern sign pat, transPattern sign t)

-- terms
transTerm :: Env -> As.Term -> IsaSign.Term
transTerm sign trm = case trm of
    QualVar (VarDecl var _ _ _) ->
        termAppl conSome $ IsaSign.Free (transVar var)

    QualOp _ (PolyId opId _ _) ts _ _ _ ->
        if opId == trueId then true
        else if opId == falseId then false
        else termAppl conSome (conDouble (transOpId sign opId ts))

    QuantifiedTerm quan varDecls phi _ ->
        let quantify q gvd phi' = case gvd of
                GenVarDecl (VarDecl var _ _ _) ->
                    termAppl (conDouble $ qname q)
                    $ Abs (IsaSign.Free $ transVar var) phi' NotCont
                GenTypeVarDecl _ ->  phi'
            qname Universal   = allS
            qname Existential = exS
            qname Unique      = ex1S
        in foldr (quantify quan) (transTerm sign phi) varDecls
    TypedTerm t _ _ _ -> transTerm sign t
    LambdaTerm pats p body _ ->
        let lambdaAbs f = if null pats then termAppl conSome
                           (Abs (IsaSign.Free $ mkVName "dummyVar")
                                    (f sign body) NotCont)
                          else termAppl conSome (foldr (abstraction sign)
                                 (f sign body)
                                 pats)
        in case p of
         -- distinguishes between partial and total lambda abstraction
         -- total lambda bodies are of type 'a' instead of type 'a option'
        Partial -> lambdaAbs transTerm
        Total   -> lambdaAbs transTotalLambda
    LetTerm As.Let peqs body _ ->
        IsaSign.Let (map (transProgEq sign) peqs) $ transTerm sign body
    TupleTerm ts@(_ : _)  _ ->
        foldl1 (binConst pairC) (map (transTerm sign) ts)
    ApplTerm t1 t2 _ -> transAppl sign Nothing t1 t2
    CaseTerm t peqs _ ->
        -- flatten case alternatives
        let alts = arangeCaseAlts sign peqs
        in case t of
        -- introduces new case statement if case variable is
        -- a term application that may evaluate to 'Some x' or 'None'
        QualVar (VarDecl decl _ _ _) ->
            Case (IsaSign.Free (transVar decl)) alts
        _ -> Case (transTerm sign t)
             [(conDouble "None", conDouble "None"),
              (App conSome (IsaSign.Free (mkVName "caseVar")) NotCont,
               Case (IsaSign.Free (mkVName "caseVar")) alts)]
    _ -> error $ "HasCASL2IsabelleHOL.transTerm " ++ showDoc trm "\n"
                ++ show trm

transAppl :: Env -> Maybe As.Type -> As.Term -> As.Term -> IsaSign.Term
transAppl s ty' t' t'' = case t'' of
    TupleTerm [] _ -> transTerm s t'
    _ -> case t' of
        QualVar (VarDecl _ ty _ _) -> transApplOp s ty t' t''
        QualOp _ (PolyId opId _ _) (TypeScheme _ ty _) _ _ _ ->
            if elem opId $ map fst bList then
               -- logical formulas are translated seperatly (transLog)
               if opId == whenElse then transWhenElse s t''
               else transLog s opId t' t''
            else transApplOp s ty t' t''
        -- distinguishes between partial and total term application
        TypedTerm tt' _ typ' _ -> transAppl s (Just typ') tt' t''
        _ -> maybe (mkApp "app" s  t' t'')
                  ( \ ty -> transApplOp s ty t' t'') ty'

mkApp :: String -> Env -> As.Term -> As.Term -> IsaSign.Term
mkApp s sg tt tt' = termAppl (termAppl (conDouble s) (transTerm sg tt))
                         (transTerm sg tt')

transApplOp :: Env -> As.Type -> As.Term -> As.Term -> IsaSign.Term
transApplOp s ty tt tt' = if isPredType ty then mkApp "pApp" s  tt tt'
    else case getTypeAppl ty of
            (TypeName tid _ 0, [_, _]) | isArrow tid ->
                if isPartialArrow tid then mkApp "app" s tt tt'
                   else mkApp "apt" s tt tt'
            _ -> mkApp "app" s tt tt'

-- translation formulas with logical connectives
transLog :: Env -> Id -> As.Term -> As.Term -> IsaSign.Term
transLog sign opId opTerm t = case t of
 TupleTerm [l' , r'] _
  | opId == andId  -> binConj l r
  | opId == orId   -> binDisj l r
  | opId == implId -> binImpl l r
  | opId == infixIf -> binImpl r l
  | opId == eqvId  -> binEq  l r
  | opId == exEq   -> binConj (binEq l r) $
                      binConj (termAppl defOp l) $
                      termAppl defOp r
  | opId == eqId -> binEq l r
  where l = transTerm sign l'
        r = transTerm sign r'
 _ | opId == notId  -> termAppl notOp (transTerm sign t)
   | opId == defId  -> termAppl defOp (transTerm sign t)
   | otherwise -> termAppl (transTerm sign opTerm) (transTerm sign t)

-- | when else statement
transWhenElse :: Env -> As.Term -> IsaSign.Term
transWhenElse sign t =
    case t of
      TupleTerm terms _ ->
        let ts = (map (transTerm sign) terms)
        in case ts of
           [i, c, e] -> If c i e NotCont
           _ -> error "HasCASL2IsabelleHOL.transWhenElse.tuple"
      _ -> error "HasCASL2IsabelleHOL.transWhenElse"

-- * translation of lambda abstractions

-- form Abs(pattern term)
abstraction :: Env -> As.Term -> IsaSign.Term -> IsaSign.Term
abstraction sign pat body =
    Abs (transPattern sign pat) body NotCont

-- translation of lambda patterns
-- a pattern keeps his type 't', isn't translated to 't option'
transPattern :: Env -> As.Term -> IsaSign.Term
transPattern _ (QualVar (VarDecl var _ _ _)) =
  IsaSign.Free (transVar var)
transPattern sign (TupleTerm terms@(_ : _)  _) =
    foldl1 (binConst isaPair) $ map (transPattern sign) terms
transPattern _ (QualOp _ (PolyId opId _ _) _ _ _ _) =
    conDouble $ showIsaConstT opId baseSign
transPattern sign (TypedTerm t _ _ _) = transPattern sign t
transPattern sign (ApplTerm t1 t2 _) =
    App (transPattern sign t1) (transPattern sign t2) NotCont
transPattern sign t = transTerm sign t

-- translation of total lambda abstraction bodies
transTotalLambda :: Env -> As.Term -> IsaSign.Term
transTotalLambda _ (QualVar (VarDecl var _ _ _)) =
  IsaSign.Free (transVar var)
transTotalLambda sign t@(QualOp _ (PolyId opId _ _) _ _ _ _) =
  if opId == trueId || opId == falseId then transTerm sign t
    else conDouble $ showIsaConstT opId baseSign
transTotalLambda sign (ApplTerm term1 term2 _) =
  termAppl (transTotalLambda sign term1) $ transTotalLambda sign term2
transTotalLambda sign (TypedTerm t _ _ _) = transTotalLambda sign t
transTotalLambda sign (LambdaTerm pats part body _) =
  case part of
    Partial -> lambdaAbs transTerm
    Total   -> lambdaAbs transTotalLambda
  where
    lambdaAbs f =
      if (null pats) then Abs (IsaSign.Free (mkVName "dummyVar"))
                               (f sign body) NotCont
--      if (null pats) then Abs [("dummyVar", noType)]
        else foldr (abstraction sign) (f sign body) pats
transTotalLambda sign (TupleTerm terms@(_ : _) _) =
  foldl1 (binConst isaPair) $ map (transTotalLambda sign) terms
transTotalLambda sign (CaseTerm t pEqs _) =
  Case (transTotalLambda sign t) $ map transCaseAltTotal pEqs
  where transCaseAltTotal (ProgEq pat trm _) =
                (transPat sign pat, transTotalLambda sign trm)
transTotalLambda sign t = transTerm sign t

-- * translation of case alternatives

{- Annotation concerning Patterns:
     Following the HasCASL-Summary and the limits of the encoding
     from HasCASL to Isabelle/HOL patterns may take the form:
        QualVar, QualOp, ApplTerm, TupleTerm and TypedTerm
-}

-- Input: List of case alternative (one pattern per term)
-- Functionality: Tests wheter pattern is a variable -> case alternative is
--                translated
arangeCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
arangeCaseAlts sign peqs
  | and (map patIsVar peqs) = map (transCaseAlt sign) peqs
  | otherwise               = sortCaseAlts sign peqs


{- Input: List of case alternatives, that patterns does consist of
        datatype constructors (with arguments) or tupels
   Functionality: Groups case alternatives by leading
        pattern-constructor each pattern group is flattened
-}
sortCaseAlts :: Env -> [ProgEq]-> [(IsaSign.Term, IsaSign.Term)]
sortCaseAlts sign peqs =
  let consList
        | null peqs = error "No case alternatives."
        | otherwise = getCons sign (getName (head peqs))
      groupedByCons = nubOrd (map (groupCons peqs) consList)
  in  map (flattenPattern sign) groupedByCons

-- Returns a list of the constructors of the used datatype
getCons :: Env -> Id -> [Id]
getCons sign tyId =
  extractIds (typeDefn (findInMap tyId (typeMap sign)))
  where extractIds (DatatypeDefn (DataEntry _ _ _ _ _ altDefns)) =
          catMaybes $ map stripConstruct $ Set.toList altDefns
        extractIds _ = error "HasCASL2Isabelle.extractIds"
        stripConstruct (Construct i _ _ _) = i
        findInMap :: Ord k => k -> Map.Map k a -> a
        findInMap k m = maybe (error "HasCASL2isabelleHOL.findInMap") id $
                Map.lookup k m

-- Extracts the type of the used datatype in case patterns
getName :: ProgEq -> Id
getName (ProgEq pat _ _) = (getTypeName pat)

getTypeName :: As.Term -> Id
getTypeName p =
   case p of
     QualVar (VarDecl _ ty _ _) -> name ty
     QualOp _ _ (TypeScheme _ ty _) _ _ _ -> name ty
     TypedTerm _ _ ty _ -> name ty
     ApplTerm t _ _ -> getTypeName t
     TupleTerm (t : _) _ -> getTypeName t
     _  -> error "HasCASL2IsabelleHOL.getTypeName"
   where name tp = case getTypeAppl tp of
             (TypeName tyId _ 0, tyArgs) -> let num = length tyArgs in
                 if isArrow tyId && num == 2 then
                    name $ head $ tail tyArgs
                 else if isProductId tyId && num > 1 then
                    name $ head tyArgs
                 else tyId
             _ -> error "HasCASL2IsabelleHOL.name (of type)"

-- Input: Case alternatives and name of one constructor
-- Functionality: Filters case alternatives by constructor's name
groupCons :: [ProgEq] -> Id -> [ProgEq]
groupCons peqs name = filter hasSameName peqs
  where hasSameName (ProgEq pat _ _) =
           hsn pat
        hsn pat =
          case pat of
            QualOp _ (PolyId n _ _) _ _ _ _ -> n == name
            ApplTerm t1 _ _ -> hsn t1
            TypedTerm t _ _ _ -> hsn t
            TupleTerm _ _ -> True
            _ -> False

-- Input: List of case alternatives with same leading constructor
-- Functionality: Tests whether the constructor has no arguments, if so
--                translates case alternatives
flattenPattern :: Env -> [ProgEq] -> (IsaSign.Term, IsaSign.Term)
flattenPattern sign peqs = case peqs of
  [] -> error "Missing constructor alternative in case pattern."
  [h] -> transCaseAlt sign h
  -- at this stage there are patterns left which use 'ApplTerm' or 'TupleTerm'
  -- or the 'TypedTerm' variant of one of them
  _ -> let m = concentrate (matricize peqs) sign in
              transCaseAlt sign (ProgEq (shrinkPat m) (term m) nullRange)

data CaseMatrix = CaseMatrix
    { patBrand :: PatBrand
    , cons     :: Maybe As.Term
    , args     :: [As.Term]
    , newArgs  :: [As.Term]
    , term     :: As.Term
    } deriving (Show, Eq, Ord)

data PatBrand = Appl | Tuple | QuOp | QuVar deriving (Show, Eq, Ord)

{- First of all a matrix is allocated (matriArg) with the arguments of a
 constructor resp.  of a tuple. They're binded with the term, that would
 be executed if the pattern matched.  Then the resulting list of
 matrices is grouped by the leading argument. (groupArgs) Afterwards -
 if a list of grouped arguments has more than one element - the last
 pattern argument (in the list 'patterns') is replaced by a new variable.
 n patterns are reduced to one pattern.
 This procedure is repeated until there's only one case alternative
 for each constructor.
  -}

-- Functionality: turns ProgEq into CaseMatrix
matricize :: [ProgEq] -> [CaseMatrix]
matricize = map matriPEq

matriPEq :: ProgEq -> CaseMatrix
matriPEq (ProgEq pat altTerm _) = matriArg pat altTerm

matriArg :: As.Term -> As.Term -> CaseMatrix
matriArg pat cTerm =
  case pat of
    ApplTerm t1 t2 _ -> let (c, p) = stripAppl t1 (Nothing, []) in CaseMatrix
        { patBrand = Appl,
          cons     = c,
          args     = p ++ [t2],
          newArgs  = [],
          term     = cTerm }
    TupleTerm ts _ -> CaseMatrix
        { patBrand = Tuple,
          cons     = Nothing,
          args     = ts,
          newArgs  = [],
          term     = cTerm }
    TypedTerm t _ _ _ -> matriArg t cTerm
    qv@(QualVar _) -> CaseMatrix
        { patBrand = QuVar,
          cons     = Nothing,
          args     = [qv],
          newArgs  = [],
          term     = cTerm }
    qo@(QualOp _ _ _ _ _ _) -> CaseMatrix
        { patBrand = QuOp,
          cons     = Nothing,
          args     = [qo],
          newArgs  = [],
          term     = cTerm }
    _ -> error "HasCASL2IsabelleHOL.matriArg"
-- Assumption: The innermost term of a case-pattern consisting of a ApplTerm
--             is a QualOp, that is a datatype constructor
  where stripAppl ct tp = case ct of
            TypedTerm (ApplTerm q@(QualOp _ _ _ _ _ _) t' _) _ _ _ ->
                (Just q, [t'] ++ snd tp)
            TypedTerm (ApplTerm (TypedTerm
              q@(QualOp _ _ _ _ _ _) _ _ _) t' _) _ _ _ ->
                (Just q, [t'] ++ snd tp)
            TypedTerm (ApplTerm t' t'' _) _ _ _ ->
              stripAppl t' (fst tp, [t''] ++ snd tp)
            ApplTerm q@(QualOp _ _ _ _ _ _) t' _ -> (Just q, [t'] ++ snd tp)
            ApplTerm (TypedTerm
              q@(QualOp _ _ _ _ _ _) _ _ _) t' _ -> (Just q, [t'])
            ApplTerm t' t'' _ -> stripAppl t' (fst tp, [t''] ++ snd tp)
            q@(QualOp _ _ _ _ _ _) -> (Just q, snd tp)
            _ -> (Nothing, [ct] ++ snd tp)

-- Input: List with CaseMatrix of same leading constructor pattern
-- Functionality: First: Groups CMs so that these CMs are in one list
--                that only differ in their last argument
--                then: reduces list of every CMslist to one CM
concentrate :: [CaseMatrix] -> Env -> CaseMatrix
concentrate cmxs sign = case map (redArgs sign) $ nubOrd
    $ map (groupByArgs cmxs) [0..(length cmxs-1)] of
  [h] -> h
  l -> concentrate l sign

groupByArgs :: [CaseMatrix] -> Int -> [CaseMatrix]
groupByArgs cmxs i
  | and (map null (map args cmxs)) = cmxs
  | otherwise                      = (filter equalPat cmxs)
  where patE = init (args (cmxs !! i))
        equalPat cmx = isSingle (args cmx) || init (args cmx) == patE

redArgs :: Env -> [CaseMatrix] -> CaseMatrix
redArgs sign cmxs
  | and (map (testPatBrand Appl) cmxs)  = redAppl cmxs sign
  | and (map (testPatBrand Tuple) cmxs) = redAppl cmxs sign
  | isSingle cmxs                       = head cmxs
  | otherwise                           = head cmxs
  where testPatBrand pb cmx = pb == patBrand cmx

{- Input: List of CMs thats leading constructor and arguments except
       the last one are equal
   Functionality: Reduces n CMs to one with same last argument in
       pattern (perhaps a new variable
-}
redAppl :: [CaseMatrix] -> Env -> CaseMatrix
redAppl cmxs sign
  | and (map null (map args cmxs)) = head cmxs
  | isSingle cmxs                  =
      (head cmxs) { args     = init $ args $ head cmxs,
                    newArgs  = last (args $ head cmxs) : newArgs (head cmxs) }
  | and (map termIsVar lastArgs)        = substVar (head cmxs)
  | otherwise                           = substTerm (head cmxs)
   where terms = map term cmxs
         lastArgs = map last (map args cmxs)
         varName = "caseVar" ++ show (length (args (head cmxs)))
         varId = (mkId [(mkSimpleId varName)])
         newVar = QualVar (VarDecl varId (TypeName varId rStar 1)
                           As.Other nullRange)
         newPeqs = (map newProgEq (zip lastArgs terms))
         newPeqs' = recArgs sign newPeqs
         substVar cmx
           | null (args cmx)     = cmx
           | isSingle (args cmx) =
               cmx { args    = [],
                     newArgs = last(args cmx) : (newArgs cmx) }
           | otherwise                =
               cmx { args    = init (args cmx),
                     newArgs = last(args cmx) : (newArgs cmx) }
         substTerm cmx
           | null (args cmx)     = cmx
           | isSingle (args cmx) =
               cmx { args    = [],
                     newArgs = newVar : (newArgs cmx),
                     term    = CaseTerm newVar newPeqs' nullRange }
           | otherwise                =
               cmx { args    = init(args cmx),
                     newArgs = newVar : (newArgs cmx),
                     term    = CaseTerm newVar newPeqs' nullRange }
         newProgEq (p, t) = ProgEq p t nullRange

-- Input: ProgEqs that were build to replace an argument
--        with a case statement
-- Functionality:
recArgs :: Env -> [ProgEq] -> [ProgEq]
recArgs sign peqs
  | isSingle groupedByCons
      || null groupedByCons = []
  | otherwise               = doPEQ groupedByCons []
  where consList
          | null peqs = error "No case alternatives."
          | otherwise    = getCons sign (getName (head peqs))
        groupedByCons = map (groupCons peqs) consList
        doPEQ [] res = res
        doPEQ (g:gByCs) res
          | isSingle g = doPEQ gByCs (res ++ g)
          | otherwise  = doPEQ gByCs (res ++ [(toPEQ (testPEQs sign g))])
        toPEQ cmx = ProgEq (shrinkPat cmx) (term cmx) nullRange
        testPEQs sig ps
          | null peqs = error "HasCASL2IsabelleHOL.testPEQs"
          | otherwise = concentrate (matricize ps) sig

-- accumulates arguments of caseMatrix to one pattern
shrinkPat :: CaseMatrix -> As.Term
shrinkPat cmx =
  case patBrand cmx of
    Appl  -> case cons cmx of
               Just c ->  foldl mkApplT c ((args cmx) ++ (newArgs cmx))
               Nothing -> error "HasCASL2IsabelleHOL.shrinkPat"
    Tuple -> TupleTerm (args cmx ++ newArgs cmx) nullRange
    QuOp  -> head (args cmx)
    _     -> head (newArgs cmx)
  where mkApplT t1 t2 = ApplTerm t1 t2 nullRange

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
    QualOp _ _ _ _ _ _ -> True
    TypedTerm tr _ _ _ -> termHasNoArg tr
    _                  -> False

transCaseAlt :: Env -> ProgEq -> (IsaSign.Term, IsaSign.Term)
transCaseAlt sign (ProgEq pat trm _) =
  (transPat sign pat, (transTerm sign trm))

transPat :: Env -> As.Term -> IsaSign.Term
transPat _ (QualVar (VarDecl var _ _ _)) =
    IsaSign.Free (transVar var)
transPat sign (ApplTerm term1 term2 _) =
    termAppl (transPat sign term1) (transPat sign term2)
transPat sign (TypedTerm trm _ _ _) = transPat sign trm
transPat sign (TupleTerm terms@(_ : _) _) =
    foldl1 (binConst isaPair) (map (transPat sign) terms)
transPat _ (QualOp _ (PolyId i _ _) _ _ _ _) =
    conDouble (showIsaConstT i baseSign)
transPat _ _ = error "HasCASL2IsabelleHOL.transPat"

-- | apply binary operation to arguments
binConst :: String -> IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binConst s = binVNameAppl $ mkVName s

-- | upper case curried pair constructor
isaPair :: String
isaPair = "Pair"
