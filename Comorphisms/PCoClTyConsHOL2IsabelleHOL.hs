{- |
Module      :  $Header$
Copyright   :  (c) Sonja Groening, C. Maeder, Uni Bremen 2003-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL to Isabelle-HOL.
-}

module Comorphisms.PCoClTyConsHOL2IsabelleHOL
    (PCoClTyConsHOL2IsabelleHOL(..)) where

import Logic.Logic as Logic
import Logic.Comorphism
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import Common.AS_Annotation (Named(..))

import Data.List
import Data.Maybe

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le as Le
import HasCASL.As as As
import HasCASL.AsUtils
import HasCASL.Builtin

import Isabelle.IsaSign as Isa
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

-- | The identity of the comorphism
data PCoClTyConsHOL2IsabelleHOL = PCoClTyConsHOL2IsabelleHOL deriving Show

instance Language PCoClTyConsHOL2IsabelleHOL -- default definition is okay

instance Comorphism PCoClTyConsHOL2IsabelleHOL
               HasCASL Sublogic
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () Isa.Sentence () ()
               Isa.Sign
               IsabelleMorphism () () ()  where
    sourceLogic PCoClTyConsHOL2IsabelleHOL = HasCASL
    sourceSublogic PCoClTyConsHOL2IsabelleHOL = noSubtypes
    targetLogic PCoClTyConsHOL2IsabelleHOL = Isabelle
    mapSublogic PCoClTyConsHOL2IsabelleHOL _ = ()
    map_theory PCoClTyConsHOL2IsabelleHOL = mkTheoryMapping transSignature
                   (map_sentence PCoClTyConsHOL2IsabelleHOL)
    map_morphism = mapDefaultMorphism
    map_sentence PCoClTyConsHOL2IsabelleHOL sign phi =
       case transSentence sign phi of
         Nothing   -> warning (mkSen true)
                           "translation of sentence not implemented" nullRange
         Just (ts) -> return $ mkSen ts
    map_symbol = errMapSymbol

-- * Signature
baseSign :: BaseSig
baseSign = MainHC_thy

transSignature :: Env -> Result (Isa.Sign,[Named Isa.Sentence])
transSignature sign =
  return (Isa.emptySign {
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
     let infos = opInfos ops
     in if isSingle infos then
            let transOp = transOpInfo (head infos)
            in case transOp of
                 Just op ->
                     Map.insert (mkVName $ showIsaConstT name baseSign) op m
                 Nothing -> m
          else
            let transOps = map transOpInfo infos
            in  foldl (\ m' (transOp,i) ->
                           case transOp of
                             Just typ -> Map.insert
                                 (mkVName $ showIsaConstIT name i baseSign)
                                 typ m'
                             Nothing   -> m')
                      m (zip transOps [1::Int ..])

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

data Option a = Option { isPartial :: Bool, val :: a }
              deriving Eq

partialVal, totalVal :: a -> Option a
partialVal a = Option { isPartial = True, val = a } 
totalVal a = Option { isPartial = False, val = a } 

mkOption :: Bool -> a -> Option a
mkOption b a = Option { isPartial = b, val = a } 

mapOption :: (a -> b) -> Option a -> Option b
mapOption f o = Option { isPartial = isPartial o, val = f $ val o }

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
                 p = isPartialArrow tid
             in mkFunType (transType t1) $
                    if isPredType t then boolType
                       else (if p
                             then mkOptionType
                             else id) $ transType t2
          else if isProductId tid && num > 1 then
             foldl1 prodType $ map transType tyArgs
          else Type (showIsaTypeT tid baseSign) [] 
                   $ map transType tyArgs
       else TFree (showIsaTypeT tid baseSign) []
            -- type arguments are not allowed here!
   _ -> error $ "transType " ++ showPretty t "\n" ++ show t

data FunType = NoFun | BoolVal | FunType FunType FunType | PartialVal FunType
             deriving Eq

isPartialVal :: FunType -> Bool
isPartialVal t = case t of 
    PartialVal _ -> True
    _ -> False

isPartialFun :: FunType -> Bool
isPartialFun t = case t of
    FunType _ r -> isPartialVal r
    _ -> False

funType :: Type -> FunType
funType t = case getTypeAppl t of
   (TypeName tid _ n, tyArgs) | n == 0 ->
       if tid == unitTypeId && null tyArgs then BoolVal
       else case tyArgs of 
              [arg, res] | isArrow tid ->
                let tArg = funType arg
                    tRes = funType res
                in FunType tArg $ 
                   (if tRes /= BoolVal && isPartialArrow tid then PartialVal
                    else id) tRes
              _ -> NoFun 
   _ -> NoFun

-- * translation of a datatype declaration

transDatatype :: TypeMap -> DomainTab
transDatatype tm = map transDataEntry (Map.fold extractDataypes [] tm)
  where extractDataypes ti des = case typeDefn ti of
                                   DatatypeDefn de -> des++[de]
                                   _               -> des

-- datatype with name (tyId) + args (tyArgs) and alternatives
transDataEntry :: DataEntry -> [DomainEntry]
transDataEntry (DataEntry _ tyId _ tyArgs _ alts) =
    -- only free types are allowed
    [(transDName tyId tyArgs, map transAltDefn alts)]
  where transDName ti ta = Type (showIsaTypeT ti baseSign) []
                           $ map transTypeArg ta

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
transAltDefn _ = error "PCoClTyConsHOL2IsabelleHOL.transAltDefn"

-- * Formulas

-- simple variables
transVar :: Var -> VName
transVar v = mkVName $ showIsaConstT v baseSign

transSentence :: Env -> Le.Sentence -> Maybe Isa.Term
transSentence sign s = case s of
    Le.Formula t      -> Just (snd $ transTerm sign t)
    DatatypeSen _     -> Nothing
    ProgEqSen _ _ _pe -> Nothing

-- disambiguate operation names
transOpId :: Env -> UninstOpId -> TypeScheme -> String
transOpId sign op ts =
  case (do ops <- Map.lookup op (assumps sign)
           if isSingle (opInfos ops) then return $ showIsaConstT op baseSign
             else do i <- elemIndex ts (map opType (opInfos ops))
                     return $ showIsaConstIT op (i+1) baseSign) of
    Just str -> str
    Nothing  -> error $ "transOpId " ++ showIsaConstT op baseSign

transProgEq :: Env -> ProgEq -> (Isa.Term, Isa.Term)
transProgEq sign (ProgEq pat trm _) =
    let op = transTerm sign pat
        ot = transTerm sign trm
    in {- if isPartial op || isPartial ot then
           (someTerm op, someTerm ot)
       else -} (snd op, snd ot)

someTerm :: Option Isa.Term -> Isa.Term
someTerm o = (if isPartial o then id else termAppl conSome) $ val o 

-- terms
transTerm :: Env -> As.Term -> (FunType, Isa.Term)
transTerm sign trm = case trm of
    QualVar (VarDecl var t _ _) -> (funType t,  
        Isa.Free (transVar var) $ transType t)
    QualOp _ (InstOpId opId _ _) ts@(TypeScheme _ ty _) _ ->
        if opId == trueId then (BoolVal, true)
        else if opId == falseId then (BoolVal, false)
             else (funType ty, 
                   conDouble $ transOpId sign opId ts)
    QuantifiedTerm quan varDecls phi _ ->
        let quantify q gvd phi' = case gvd of
                GenVarDecl (VarDecl var typ _ _) ->
                    termAppl (conDouble $ qname q)
                    $ Abs (con $ transVar var) 
                          (transType typ) phi' NotCont
                GenTypeVarDecl _ ->  phi'
            qname Universal   = allS
            qname Existential = exS
            qname Unique      = ex1S
            (_, psi) = transTerm sign phi
        in (BoolVal, foldr (quantify quan) psi varDecls)
    TypedTerm t _ _ _ -> transTerm sign t
    LambdaTerm pats _ body _ ->
        let tPats = map (fst . transTerm sign) pats 
            (bodyTy, bodyTrm) = transTerm sign body
        in ( foldr FunType bodyTy tPats
           , foldr (abstraction sign) bodyTrm pats )
    LetTerm As.Let peqs body _ -> 
        let (bTy, bTrm) = transTerm sign body
        in (bTy, Isa.Let (map (transProgEq sign) peqs) bTrm)
    TupleTerm ts@(_ : _)  _ -> 
        let (tys, tts) = unzip $ map (transTerm sign) ts
        in (if any isPartialVal tys then PartialVal NoFun else NoFun,
            foldl1 (binConst pairC) tts)
    ApplTerm t1 t2 _ -> mkApp sign t1 t2 -- transAppl sign Nothing t1 t2
{-
    CaseTerm t peqs _ ->
        -- flatten case alternatives
        let alts = arangeCaseAlts sign peqs
        in partialVal $ case t of
        -- introduces new case statement if case variable is
        -- a term application that may evaluate to 'Some x' or 'None'
        QualVar (VarDecl decl _ _ _) -> 
            Case (Isa.Free (transVar decl) noType) alts
        _ -> Case (snd $ transTerm sign t)
             [(conDouble "None", conDouble "None"),
              (App conSome (Isa.Free (mkVName "caseVar") noType) NotCont,
               Case (Isa.Free (mkVName "caseVar") noType) alts)]
-}
    _ -> error $ "PCoClTyConsHOL2IsabelleHOL.transTerm " ++ showPretty trm "\n"
                ++ show trm


{-
transAppl :: Env -> Maybe As.Type -> As.Term -> As.Term -> (FunType, Isa.Term)
transAppl s typ t' t'' = case t'' of
    TupleTerm [] _ -> transTerm s t'
    _ -> case t' of
        QualVar (VarDecl _ ty _ _) -> transApplOp s ty t' t''
        QualOp _ (InstOpId opId _ _) (TypeScheme _ ty _) _ ->
            if elem opId $ map fst bList then
               -- logical formulas are translated seperatrly (transLog)
               if opId == whenElse then transWhenElse s t''
               else transLog s opId t' t''
            else transApplOp s ty t' t''
        -- distinguishes between partial and total term application
        TypedTerm tt' _ typ' _ -> transAppl s (Just typ') tt' t''
        _ -> maybe (mkApp "app" s  t' t'')
                  ( \ ty -> transApplOp s ty t' t'') typ
-}

noneTrm :: Isa.Term
noneTrm = conDouble "None"

varTrm :: Isa.Term
varTrm = conDouble "x"

mkCaseTerm :: Isa.Term -> (Isa.Term -> Isa.Term) -> Isa.Term
mkCaseTerm trm mkBody = 
    Isa.Case trm 
      [ (noneTrm, noneTrm)
      , (termAppl conSome varTrm, mkBody varTrm)]

mkApp :: Env -> As.Term -> As.Term -> (FunType, Isa.Term)
mkApp sg tt tt' = 
    let (fTy, fTrm) = transTerm sg tt
        (aTy, aTrm) = transTerm sg tt
    in case fTy of
         FunType a r@(PartialVal _) ->
            (r, termAppl (termAppl (conDouble 
                (if isPartialVal aTy then "appl1" else "appl2")) fTrm) aTrm)
         FunType a r -> if isPartialVal aTy then
            (PartialVal r, termAppl (termAppl (conDouble "appl3") fTrm) aTrm)
             else (r, termAppl fTrm aTrm)
         PartialVal (FunType a r@(PartialVal _)) ->
            (r, termAppl (termAppl (conDouble 
                (if isPartialVal aTy then "appl4" else "appl5")) fTrm) aTrm)
         PartialVal (FunType a r) ->
            (PartialVal r, termAppl (termAppl (conDouble 
                (if isPartialVal aTy then "appl6" else "appl7")) fTrm) aTrm)
         _ -> error "not a function type"

{-
transApplOp :: Env -> As.Type -> As.Term -> As.Term -> (FunType, Isa.Term)
transApplOp s typ tt tt' = if isPredType typ then mkApp "pApp" s  tt tt'
    else case getTypeAppl typ of
            (TypeName tid _ 0, [_, _]) | isArrow tid ->
                if isPartialArrow tid then mkApp "app" s tt tt'
                   else mkApp "apt" s tt tt'
            _ -> mkApp "app" s tt tt'

-- translation formulas with logical connectives
transLog :: Env -> Id -> As.Term -> As.Term -> Option Isa.Term
transLog sign opId opTerm t = partialVal $ case t of
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
  where l = someTerm $ transTerm sign l'
        r = someTerm $ transTerm sign r'
 _ | opId == notId  -> termAppl notOp (someTerm $ transTerm sign t)
   | opId == defId  -> termAppl defOp (someTerm $ transTerm sign t)
   | otherwise -> termAppl (someTerm $ transTerm sign opTerm) 
                  $ someTerm $ transTerm sign t

-- | when else statement
transWhenElse :: Env -> As.Term -> Option Isa.Term
transWhenElse sign t =
    case t of
      TupleTerm terms _ ->
        let ts = (map (someTerm . transTerm sign) terms)
        in case ts of
           [i, c, e] -> partialVal $ If c i e NotCont
           _ -> error "PCoClTyConsHOL2IsabelleHOL.transWhenElse.tuple"
      _ -> error "PCoClTyConsHOL2IsabelleHOL.transWhenElse"
-}

-- * translation of lambda abstractions

-- form Abs(pattern term)
abstraction :: Env -> As.Term -> Isa.Term -> Isa.Term
abstraction sign pat body =
    Abs (snd $ transTerm sign pat) (getType pat) body NotCont
    where
    getType t =
      case t of
        QualVar (VarDecl _ typ _ _) -> transType typ
        TypedTerm _ _ typ _         -> transType typ
        TupleTerm terms _           -> evalTupleType terms
        _                           ->
          error "PCoClTyConsHOL2IsabelleHOL.abstraction"
    evalTupleType t = foldr1 prodType (map getType t)

-- * translation of case alternatives

{- Annotation concerning Patterns:
     Following the HasCASL-Summary and the limits of the encoding
     from HasCASL to Isabelle/HOL patterns may take the form:
        QualVar, QualOp, ApplTerm, TupleTerm and TypedTerm
-}

-- Input: List of case alternative (one pattern per term)
-- Functionality: Tests wheter pattern is a variable -> case alternative is
--                translated
arangeCaseAlts :: Env -> [ProgEq]-> [(Isa.Term, Isa.Term)]
arangeCaseAlts sign peqs
  | and (map patIsVar peqs) = map (transCaseAlt sign) peqs
  | otherwise               =  sortCaseAlts sign peqs


{- Input: List of case alternatives, that patterns does consist of
        datatype constructors (with arguments) or tupels
   Functionality: Groups case alternatives by leading
        pattern-constructor each pattern group is flattened
-}
sortCaseAlts :: Env -> [ProgEq]-> [(Isa.Term, Isa.Term)]
sortCaseAlts sign peqs =
  let consList
        | null peqs = error "No case alternatives."
        | otherwise = getCons sign (getName (head peqs))
      groupedByCons = Data.List.nub (map (groupCons peqs) consList)
  in  map (flattenPattern sign) groupedByCons

-- Returns a list of the constructors of the used datatype
getCons :: Env -> TypeId -> [UninstOpId]
getCons sign tyId =
  extractIds (typeDefn (findInMap tyId (typeMap sign)))
  where extractIds (DatatypeDefn (DataEntry _ _ _ _ _ altDefns)) =
          catMaybes (map stripConstruct altDefns)
        extractIds _ = error "PCoClTyConsHOL2Isabelle.extractIds"
        stripConstruct (Construct i _ _ _) = i
        findInMap :: Ord k => k -> Map.Map k a -> a
        findInMap k m = maybe 
              (error "PCoClTyConsHOL2isabelleHOL.findInMap") id $
                Map.lookup k m

-- Extracts the type of the used datatype in case patterns
getName :: ProgEq -> TypeId
getName (ProgEq pat _ _) = (getTypeName pat)

getTypeName :: Pattern -> TypeId
getTypeName p =
   case p of
     QualVar (VarDecl _ typ _ _)       -> name typ
     QualOp _ _ (TypeScheme _ typ _) _ -> name typ
     TypedTerm _ _ typ _               -> name typ
     ApplTerm  t _ _                   -> getTypeName t
     TupleTerm ts _                    -> getTypeName (head ts)
     _  -> error "PCoClTyConsHOL2IsabelleHOL.getTypeName"
   where name tp = case getTypeAppl tp of
             (TypeName tyId _ 0, tyArgs) -> let num = length tyArgs in
                 if isArrow tyId && num == 2 then
                    name $ head $ tail tyArgs
                 else if isProductId tyId && num > 1 then
                    name $ head tyArgs
                 else tyId
             _ -> error "PCoClTyConsHOL2IsabelleHOL.name (of type)"

-- Input: Case alternatives and name of one constructor
-- Functionality: Filters case alternatives by constructor's name
groupCons :: [ProgEq] -> UninstOpId -> [ProgEq]
groupCons peqs name = filter hasSameName peqs
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
flattenPattern :: Env -> [ProgEq] -> (Isa.Term, Isa.Term)
flattenPattern sign peqs = case peqs of
  [] -> error "Missing constructor alternative in case pattern."
  [h] -> transCaseAlt sign h
  -- at this stage there are patterns left which use 'ApplTerm' or 'TupleTerm'
  -- or the 'TypedTerm' variant of one of them
  _ -> let m = concentrate (matricize peqs) sign in
              transCaseAlt sign (ProgEq (shrinkPat m) (term m) nullRange)

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
    _                   -> error "PCoClTyConsHOL2IsabelleHOL.matriArg"
-- Assumption: The innermost term of a case-pattern consisting of a ApplTerm
--             is a QualOp, that is a datatype constructor
  where stripAppl ct tp = case ct of
            TypedTerm (ApplTerm q@(QualOp _ _ _ _) t' _) _ _ _ ->
                (Just q, [t'] ++ snd tp)
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
            _                                -> (Nothing, [ct] ++ snd tp)

-- Input: List with CaseMatrix of same leading constructor pattern
-- Functionality: First: Groups CMs so that these CMs are in one list
--                that only differ in their last argument
--                then: reduces list of every CMslist to one CM
concentrate :: [CaseMatrix] -> Env -> CaseMatrix
concentrate cmxs sign = case map (redArgs sign) $
                        nub $ map (groupByArgs cmxs) [0..(length cmxs-1)] of
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
                           Other nullRange)
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
          | null peqs = error "PCoClTyConsHOL2IsabelleHOL.testPEQs"
          | otherwise = concentrate (matricize ps) sig

-- accumulates arguments of caseMatrix to one pattern
shrinkPat :: CaseMatrix -> As.Term
shrinkPat cmx =
  case patBrand cmx of
    Appl  -> case cons cmx of
               Just c ->  foldl mkApplT c ((args cmx) ++ (newArgs cmx))
               Nothing -> error "PCoClTyConsHOL2IsabelleHOL.shrinkPat"
    Tuple -> TupleTerm ((args cmx) ++ (newArgs cmx)) nullRange
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

transCaseAlt :: Env -> ProgEq -> (Isa.Term, Isa.Term)
transCaseAlt sign (ProgEq pat trm _) =
  (snd $ transTerm sign pat, snd $ transTerm sign trm)
