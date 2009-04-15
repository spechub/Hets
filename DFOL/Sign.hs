{- |
Module      :  $Header$
Description :  Definition of signatures for first-order logic with dependent types (DFOL)
-}

module DFOL.Sign
   ( KIND (..)
   , ARITY
   , CONTEXT (..)
   , Sign (..)
   , getVarsFromDecls
   , getVarTypeFromDecls
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
   , substitute
   , alphaRename
   ) where

import DFOL.AS_DFOL
import Common.Id
import Common.Doc
import Common.DocUtils
import Data.List
import Data.Maybe
import qualified Data.Set as Set

-- operations on a list of declarations
getVarsFromDecls :: [DECL] -> [NAME]
getVarsFromDecls ds = concatMap fst ds

getVarTypeFromDecls :: NAME -> [DECL] -> Maybe TYPE
getVarTypeFromDecls n ds = case result of
                                Just (_,t) -> Just t
                                Nothing -> Nothing
                           where result = find (\ (ns,_) -> elem n ns) ds

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
getSymbolsByKind sig kind = Set.filter (\n -> (getSymbolKind n sig) == Just kind) $ getSymbols sig

-- get the list of types of the arguments of the given symbol
getArgumentTypes :: NAME -> Sign -> Maybe [TYPE]
getArgumentTypes n sig = case typM of
                              Nothing -> Nothing
                              Just typ -> Just $ getArgumentTypesH typ
                         where typM = getSymbolType n sig

getArgumentTypesH :: TYPE -> [TYPE]
getArgumentTypesH (Pi ds t) = types1 ++ types2
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
getArgumentNames n sig = case typM of
                           Nothing -> Nothing
                           Just typ -> Just $ fillArgumentNames $ getArgumentNamesH typ
                         where typM = getSymbolType n sig

getArgumentNamesH :: TYPE -> [Maybe NAME]
getArgumentNamesH (Pi ds t) = (map Just $ getVarsFromDecls ds) ++ getArgumentNamesH t
getArgumentNamesH (Func ts t) = (take (length ts) $ repeat Nothing) ++ getArgumentNamesH t
getArgumentNamesH _ = []

fillArgumentNames :: [Maybe NAME] -> [NAME]
fillArgumentNames ns = fillArgumentNamesH ns 0

fillArgumentNamesH :: [Maybe NAME] -> Int -> [NAME]
fillArgumentNamesH [] _ = []
fillArgumentNamesH (nameM:namesM) i = case nameM of
                                           Just name -> name:(fillArgumentNamesH namesM i)
                                           Nothing -> (Token ("gen_x_" ++ show i) nullRange):(fillArgumentNamesH namesM (i+1))

-- substitutions
substitute :: NAME -> TERM -> TYPE -> TYPE
substitute _ _ Sort = Sort
substitute _ _ Form = Form
substitute n val (Univ t) = Univ $ substituteInTerm n val t
substitute n val (Func ts t) = Func (map (substitute n val) ts) (substitute n val t)
substitute n val (Pi ds t) = Pi (map (substituteInDecl n val) ds) (substitute n val t)

substituteInTerm :: NAME -> TERM -> TERM -> TERM
substituteInTerm n val (Identifier x) = if (x == n) then val else Identifier x
substituteInTerm n val (Appl f as) = Appl (substituteInTerm n val f) $ map (substituteInTerm n val) as

substituteInDecl :: NAME -> TERM -> DECL -> DECL
substituteInDecl n val (ns,t) = (ns, substitute n val t)

-- renamings
alphaRename :: TYPE -> Sign -> CONTEXT -> TYPE
alphaRename t sig cont = alphaRenameH t 0 declaredSyms 
                         where declaredSyms = Set.union (getSymbols sig) (getVars cont)  

alphaRenameH :: TYPE -> Int -> Set.Set NAME -> TYPE
alphaRenameH t i names = if (i >= length vars)
                            then t
                            else let var = vars !! i
                                     in if (Set.notMember var names) 
                                           then alphaRenameH t (i+1) $ Set.insert var names
                                           else let newVar = renameVar var $ Set.union names 
                                                      $ Set.fromList $ (take i vars) ++ (drop (i+1) vars)  
                                                    newType = substituteVar var newVar t
                                                    in alphaRenameH newType (i+1) $ Set.insert newVar names
                         where vars = getVarsDeclaredInType t
  
renameVar :: NAME -> Set.Set NAME -> NAME
renameVar var names = if (Set.notMember newVar names) then newVar else renameVar newVar names 
                      where newVar = Token ((tokStr var) ++ "1") nullRange
                         
substituteVar :: NAME -> NAME -> TYPE -> TYPE
substituteVar _ _ Sort = Sort
substituteVar _ _ Form = Form
substituteVar n1 n2 (Univ t) = Univ $ substituteVarInTerm n1 n2 t
substituteVar n1 n2 (Func ts t) = Func (map (substituteVar n1 n2) ts) (substituteVar n1 n2 t)
substituteVar n1 n2 (Pi ds t) = Pi (substituteVarInDecls n1 n2 ds) (substituteVar n1 n2 t)

substituteVarInTerm :: NAME -> NAME -> TERM -> TERM
substituteVarInTerm n1 n2 (Identifier x) = if (x == n1) then Identifier n2 else Identifier x
substituteVarInTerm n1 n2 (Appl f as) = Appl (substituteVarInTerm n1 n2 f) $ map (substituteVarInTerm n1 n2) as

substituteVarInDecls :: NAME -> NAME -> [DECL] -> [DECL]
substituteVarInDecls n1 n2 ds = map (substituteVarInDecl n1 n2) ds

substituteVarInDecl :: NAME -> NAME -> DECL -> DECL
substituteVarInDecl n1 n2 (ns,t) = (substituteVarInNames n1 n2 ns, substituteVar n1 n2 t)

substituteVarInNames :: NAME -> NAME -> [NAME] -> [NAME]
substituteVarInNames n1 n2 ns = map (\n -> if n == n1 then n2 else n) ns

-- returns a list of declared variables from within a type
getVarsDeclaredInType :: TYPE -> [NAME]
getVarsDeclaredInType (Pi ds t) = (getVarsFromDecls ds) ++ (getVarsDeclaredInType t)
getVarsDeclaredInType _ = []

-- pretty printing
instance Pretty Sign where
   pretty = printSig
instance Pretty CONTEXT where
   pretty (Context xs) = printDecls xs
instance Pretty KIND where
   pretty = printKind

printSig :: Sign -> Doc
printSig (Sign []) = text "EmptySig"
printSig (Sign ds) = vcat $ map printSigDecl ds

printSigDecl :: DECL -> Doc
printSigDecl (ns,t) = printNames ns <+> text "::" <+> pretty t

printKind :: KIND -> Doc
printKind SortKind = text "sort"
printKind FuncKind = text "func"
printKind PredKind = text "pred"
