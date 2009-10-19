{- |
Module      :  $Header$
Description :  Definition of signatures for first-order logic
               with dependent types (DFOL)
-}

module DFOL.Sign
   ( KIND (..)
   , ARITY
   , CONTEXT (..)
   , Sign (..)
   , emptyContext
   , addVarDecl
   , getVars
   , getVarType
   , emptySig
   , addSymbolDecl
   , getSymbols
   , isConstant
   , getSymbolType
   , getSymbolKind
   , getSymbolArity
   , getSymbolsByKind
   , getArgumentTypes
   , getReturnType
   , getArgumentNames
   , sigUnion
   , sigIntersection
   , isValidDecl
   , isValidVarDecl
   , getTermType
   , hasType
   , isValidType
   ) where

import DFOL.Utils
import DFOL.AS_DFOL
import Common.Id
import Common.Doc
import Common.DocUtils
import Data.List
import Data.Maybe
import qualified Common.Result as Result
import qualified Data.Set as Set
import qualified Data.Map as Map

-- symbol kinds
data KIND = SortKind
          | FuncKind
          | PredKind
            deriving (Show, Ord, Eq)

type ARITY = Int

-- contexts for DFOL
data CONTEXT = Context [DECL]
               deriving (Show, Eq)

-- the empty context
emptyContext :: CONTEXT
emptyContext = Context []

-- adds a variable declaration to the context
addVarDecl :: DECL -> CONTEXT -> CONTEXT
addVarDecl d (Context ds) = Context (ds ++ [d])

-- get the list of declared variables
getVars :: CONTEXT -> Set.Set NAME
getVars (Context ds) = Set.fromList $ getVarsFromDecls ds

-- get the variable type
getVarType :: NAME -> CONTEXT -> Maybe TYPE
getVarType n (Context ds) = getVarTypeFromDecls n ds

-- signatures for DFOL
data Sign = Sign [DECL]
            deriving (Show, Ord, Eq)

-- the empty signature
emptySig :: Sign
emptySig = Sign []

-- adds a symbol declaration to the signature
addSymbolDecl :: DECL -> Sign -> Sign
addSymbolDecl d (Sign ds) = Sign (ds ++ [d])

-- get the set of defined symbols
getSymbols :: Sign -> Set.Set NAME
getSymbols (Sign ds) = Set.fromList $ getVarsFromDecls ds

-- checks if the symbol is defined in the signature
isConstant :: NAME -> Sign -> Bool
isConstant n sig = Set.member n $ getSymbols sig

-- get the symbol type
getSymbolType :: NAME -> Sign -> Maybe TYPE
getSymbolType n (Sign ds) = getVarTypeFromDecls n ds

-- get the symbol kind
getSymbolKind :: NAME -> Sign -> Maybe KIND
getSymbolKind n sig = case (getReturnType n sig) of
                           Nothing -> Nothing
                           Just Sort -> Just SortKind
                           Just Form -> Just PredKind
                           Just _ -> Just FuncKind

-- get the symbol arity
getSymbolArity :: NAME -> Sign -> Maybe ARITY
getSymbolArity n sig = case (getArgumentTypes n sig) of
                            Nothing -> Nothing
                            Just ts -> Just $ length ts

-- get a list of symbols of the given kind
getSymbolsByKind :: Sign -> KIND -> Set.Set NAME
getSymbolsByKind sig kind =
   Set.filter (\n -> (getSymbolKind n sig) == Just kind) $ getSymbols sig

-- get the list of types of the arguments of the given symbol
getArgumentTypes :: NAME -> Sign -> Maybe [TYPE]
getArgumentTypes n sig = case typM of
                              Nothing -> Nothing
                              Just typ -> Just $ getArgumentTypesH typ
                         where typM = getSymbolType n sig

getArgumentTypesH :: TYPE -> [TYPE]
getArgumentTypesH (Pi ds t) =
  types1 ++ types2
  where types1 = concatMap (\ (ns,t1) -> take (length ns) $ repeat t1) ds
        types2 = getArgumentTypesH t
getArgumentTypesH (Func ts t) = ts ++ (getArgumentTypesH t)
getArgumentTypesH _ = []

-- get the return type of a symbol with the given type
getReturnType :: NAME -> Sign -> Maybe TYPE
getReturnType n sig = case typM of
                           Nothing -> Nothing
                           Just typ -> Just $ getReturnTypeH typ
                      where typM = getSymbolType n sig

getReturnTypeH :: TYPE -> TYPE
getReturnTypeH (Pi _ t) = getReturnTypeH t
getReturnTypeH (Func _ t) = getReturnTypeH t
getReturnTypeH t = t

-- get the argument names
getArgumentNames :: NAME -> Sign -> Maybe [NAME]
getArgumentNames n sig =
  case typM of
       Nothing -> Nothing
       Just typ -> Just $ fillArgumentNames $ getArgumentNamesH typ
  where typM = getSymbolType n sig

getArgumentNamesH :: TYPE -> [Maybe NAME]
getArgumentNamesH (Pi ds t) =
  (map Just $ getVarsFromDecls ds) ++ getArgumentNamesH t
getArgumentNamesH (Func ts t) =
  (take (length ts) $ repeat Nothing) ++ getArgumentNamesH t
getArgumentNamesH _ = []

fillArgumentNames :: [Maybe NAME] -> [NAME]
fillArgumentNames ns = fillArgumentNamesH ns 0

fillArgumentNamesH :: [Maybe NAME] -> Int -> [NAME]
fillArgumentNamesH [] _ = []
fillArgumentNamesH (nameM:namesM) i =
  case nameM of
       Just name -> name:(fillArgumentNamesH namesM i)
       Nothing -> (Token ("gen_x_" ++ show i) nullRange):
                  (fillArgumentNamesH namesM (i+1))

-- pretty printing
instance Pretty Sign where
   pretty = printSig
instance Pretty CONTEXT where
   pretty (Context xs) = printDecls xs
instance Pretty KIND where
   pretty = printKind

printSig :: Sign -> Doc
printSig (Sign []) = text "EmptySig"
printSig (Sign ds) = vcat $ map printSigDecl $ compactDecls ds

printSigDecl :: DECL -> Doc
printSigDecl (ns,t) = printNames ns <+> text "::" <+> pretty t

printKind :: KIND -> Doc
printKind SortKind = text "sort"
printKind FuncKind = text "func"
printKind PredKind = text "pred"

{- Union of signatures. The union of two DFOL signatures Sig1 and Sig2 is
   defined as the smallest valid signature containing both Sig1 and Sig2 as
   subsignatures. It is not always defined, namely in the case when the original
   signatures give conflicting definitions for the same symbol. -}
sigUnion :: Sign -> Sign -> Result.Result Sign
sigUnion sig (Sign ds) = sigUnionH (expandDecls ds) sig

sigUnionH :: [DECL] -> Sign -> Result.Result Sign
sigUnionH [] sig = Result.Result [] $ Just sig
sigUnionH (([n],t):ds) sig =
  if (isConstant n sig)
     then let Just t1 = getSymbolType n sig
              in if (t == t1)
                    then sigUnionH ds sig
                    else Result.Result [incompatibleUnionError n t t1] Nothing
     else let t1 = translate Map.empty (getSymbols sig) t
              sig1 = addSymbolDecl ([n],t1) sig
              in sigUnionH ds sig1
sigUnionH _ _ = Result.Result [] Nothing

{- Intersection of signatures. The intersection of two DFOL signatures Sig1 and
   Sig2 is defined as the largest valid signature contained both in Sig1 and
   Sig2 as a subsignature. It is always defined but may be the empty
   signature. -}
sigIntersection :: Sign -> Sign -> Result.Result Sign
sigIntersection (Sign ds) sig = sigIntersectionH (expandDecls ds) emptySig sig

sigIntersectionH :: [DECL] -> Sign -> Sign -> Result.Result Sign
sigIntersectionH [] sig _ = Result.Result [] $ Just sig
sigIntersectionH (([n],t):ds) sig sig2 =
  let present = if (isConstant n sig2)
                   then let Just t1 = getSymbolType n sig2
                        in if (t == t1)
                              then True
                              else False
                   else False
      Diagn _ valid = isValidDecl ([n],t) sig emptyContext
      in if (and [present,valid])
            then let sig1 = addSymbolDecl ([n],t) sig
                     in sigIntersectionH ds sig1 sig2
            else sigIntersectionH ds sig sig2
sigIntersectionH _ _ _ = Result.Result [] Nothing

-- determines whether a declaration is valid w.r.t. a signature and a context
isValidDecl :: DECL -> Sign -> CONTEXT -> DIAGN Bool
isValidDecl (ns,t) sig cont = andD [validNames, validType]
                              where validNames = areValidNames ns sig cont
                                    validType  = isValidType t sig cont

-- checks if a variable declaration is valid w.r.t. a signature and a context
isValidVarDecl :: DECL -> Sign -> CONTEXT -> DIAGN Bool
isValidVarDecl d@(_,t) sig cont = andD [discourseType,validDec]
                                  where discourseType = isDiscourseType t
                                        validDec = isValidDecl d sig cont

{- checks if a list of names in a declaration is valid w.r.t. a signature
   and a context -}
areValidNames :: [NAME] -> Sign -> CONTEXT -> DIAGN Bool
areValidNames names sig cont =
   if (Set.null overlap)
      then Diagn [] True
      else Diagn [redeclaredNamesError overlap cont] False
   where declaredSyms = Set.union (getSymbols sig) (getVars cont)
         newSyms      = Set.fromList names
         overlap      = Set.intersection newSyms declaredSyms

-- determines whether a type is valid w.r.t. a signature and a context
isValidType :: TYPE -> Sign -> CONTEXT -> DIAGN Bool
isValidType Sort _ _ = Diagn [] True
isValidType Form _ _ = Diagn [] True
isValidType (Univ t) sig cont = hasType t Sort sig cont
isValidType (Func ts t) sig cont =
   andD [validDoms,validCod,discourseDoms]
   where validDoms = andD $ map (\t1 -> isValidType t1 sig cont) ts
         validCod  = isValidType t sig cont
         discourseDoms = andD $ map isDiscourseType ts
isValidType (Pi [] t) sig cont = isValidType t sig cont
isValidType (Pi (d:ds) t) sig cont =
   andD [validDecl, validType]
   where validDecl = isValidVarDecl d sig cont
         validType = isValidType (Pi ds t) sig (addVarDecl d cont)

-- determines whether a type starts with Univ
isDiscourseType :: TYPE -> DIAGN Bool
isDiscourseType t = case t of
                         Univ _ -> Diagn [] True
                         _ -> Diagn [noDiscourseTypeError t] False

-- determines whether a term has the given type w.r.t. a signature and a context
hasType :: TERM -> TYPE -> Sign -> CONTEXT -> DIAGN Bool
hasType term expectedType sig cont =
   case inferredTypeM of
        Nothing -> Diagn diag False
        Just inferredType ->
           if (inferredType == expectedType)
              then Diagn [] True
              else Diagn [wrongTypeError expectedType inferredType term cont]
                         False
   where Result.Result diag inferredTypeM = getTermType term sig cont

-- determines the type of a term w.r.t. a signature and a context
-- returns type in proper and pi-recursive form
getTermType :: TERM -> Sign -> CONTEXT -> Result.Result TYPE
getTermType term sig cont = getTermTypeH (termRecForm term) sig cont

getTermTypeH ::TERM -> Sign -> CONTEXT -> Result.Result TYPE
getTermTypeH (Identifier n) sig cont =
   case fromContext of
        Just _  -> Result.Result [] fromContext
        Nothing -> case fromSig of
                        Just type1 ->
                          let type2 = renameBoundVars (piRecForm type1) sig cont
                              in Result.Result [] $ Just type2
                        Nothing ->
                          Result.Result [unknownIdentifierError n cont] Nothing
   where fromSig = getSymbolType n sig
         fromContext = getVarType n cont
getTermTypeH (Appl f [a]) sig cont =
   case typeAM of
        Nothing -> Result.Result diagA Nothing
        Just typeA ->
          case typeFM of
               Nothing -> Result.Result diagF Nothing
               Just (Func (dom:doms) cod) ->
                 if (dom == typeA)
                    then Result.Result [] $ Just $ typeProperForm
                            $ Func doms cod
                    else Result.Result [wrongTypeError dom typeA a cont] Nothing
               Just (Pi [([x],t)] typ) ->
                 if (t == typeA)
                    then Result.Result [] $ Just $ substitute x a typ
                    else Result.Result [wrongTypeError t typeA a cont] Nothing
               Just typeF ->
                 Result.Result [noFunctionTermError f typeF cont] Nothing
    where Result.Result diagF typeFM = getTermType f sig cont
          Result.Result diagA typeAM = getTermType a sig cont
getTermTypeH _ _ _ = Result.Result [] Nothing

-- renames bound variables in a type to make it valid w.r.t. a sig and a context
-- expects type in proper and pi-recursive form
renameBoundVars :: TYPE -> Sign -> CONTEXT -> TYPE
renameBoundVars t sig cont =
  let syms = Set.union (getSymbols sig) (getVars cont)
      in translate Map.empty syms t

substitute :: NAME -> TERM -> TYPE -> TYPE
substitute n val t = translate (Map.singleton n val) Set.empty t

-- ERROR MESSAGES
redeclaredNamesError :: Set.Set NAME -> CONTEXT -> Result.Diagnosis
redeclaredNamesError ns cont =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbols or variables\n" ++ show ns
                          ++ "\ndeclared previously in the context\n"
                          ++ (show $ pretty cont) ++ "\nor in the signature."
    , Result.diagPos = nullRange
    }

noFunctionTermError :: TERM -> TYPE -> CONTEXT -> Result.Diagnosis
noFunctionTermError term t cont =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Term\n" ++ (show $ pretty term)
                          ++ "\nhas the non-function type\n"
                          ++ (show $ pretty t)
                          ++ "\nin the context\n" ++ (show $ pretty cont)
                          ++ "\nand hence cannot be applied to an argument."
    , Result.diagPos = nullRange
    }

noDiscourseTypeError :: TYPE -> Result.Diagnosis
noDiscourseTypeError t =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString =
         "Type\n" ++ (show $ pretty t)
         ++ "\nis a non-discourse type (does not start with Univ) "
         ++ "and hence cannot be used as a type of an argument."
    , Result.diagPos = nullRange
    }

wrongTypeError :: TYPE -> TYPE -> TERM -> CONTEXT -> Result.Diagnosis
wrongTypeError type1 type2 term cont =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Term\n" ++ (show $ pretty term)
                          ++ "\nmust be of type "
                          ++ (show $ pretty type1) ++ "\nbut is of type\n"
                          ++ (show $ pretty type2) ++ "\nin context\n"
                          ++ (show $ pretty cont)
    , Result.diagPos = nullRange
    }

unknownIdentifierError :: NAME -> CONTEXT -> Result.Diagnosis
unknownIdentifierError n cont =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Unknown identifier\n" ++ (show $ pretty n)
                          ++ "\nin the context\n" ++ (show $ pretty cont)
    , Result.diagPos = nullRange
    }

incompatibleUnionError :: NAME -> TYPE -> TYPE -> Result.Diagnosis
incompatibleUnionError n t1 t2 =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Symbol\n" ++ (show $ pretty n)
                          ++ "\nmust have both type\n" ++ (show $ pretty t1)
                          ++ "\nand type\n" ++ (show $ pretty t2)
                          ++ "\nin the signature union and hence "
                          ++ "the union is not defined."
    , Result.diagPos = nullRange
    }
