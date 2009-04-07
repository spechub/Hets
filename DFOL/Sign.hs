{- |
Module      :  $Header$
Description :  Definition of signatures for first-order logic with dependent types (DFOL)
-}

module DFOL.Sign where

import DFOL.AS_DFOL
import Common.Doc
import Common.DocUtils
import qualified Data.Set as Set

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
getSymbols (Sign ds) = getVarsFromDecls ds 
              
-- get the symbol type
getSymbolType :: NAME -> Sign -> Maybe TYPE
getSymbolType n (Sign ds) = getTypeFromDecls n ds
    
-- contexts for DFOL
data CONTEXT = Context [DECL]   
               deriving (Show, Eq)

-- the empty context
emptyContext :: CONTEXT
emptyContext = Context []

-- adds a variable declaration to the context
addVarDecl :: DECL -> CONTEXT -> CONTEXT
addVarDecl d (Context ds) = Context (ds ++ [d])

-- get the set of declared variables
getVars :: CONTEXT -> Set.Set NAME
getVars (Context ds) = getVarsFromDecls ds 

-- get the variable type
getVarType :: NAME -> CONTEXT -> Maybe TYPE
getVarType n (Context ds) = getTypeFromDecls n ds

-- pretty printing
instance Pretty Sign where
   pretty = printSig
instance Pretty CONTEXT where
   pretty = printContext

printSig :: Sign -> Doc
printSig (Sign []) = text "EmptySig"
printSig (Sign ds) = vcat $ map printSigDecl ds 

printSigDecl :: DECL -> Doc 
printSigDecl (ns,t) = pretty ns <+> text "::" <+> pretty t

printContext :: CONTEXT -> Doc
printContext (Context xs) = pretty xs
