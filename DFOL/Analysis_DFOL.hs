{- |
Module      :  $Header$
Description :  Static analysis for first-order logic with dependent types (DFOL)
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module DFOL.Analysis_DFOL
  (
    basicAnalysis         -- static analysis of basic specifications
  , symbAnalysis          -- static analysis for symbols lists
  , symbMapAnalysis       -- static analysis for symbol map lists
   ) where

import DFOL.Utils
import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Symbol

import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import qualified Common.Result as Result
import qualified Common.AS_Annotation as Anno

import qualified Data.Set as Set
import qualified Data.Map as Map

-- BASIC SPEC ANALYSIS
basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos) ->
   Result.Result (BASIC_SPEC, ExtSign Sign Symbol, [Anno.Named FORMULA])
basicAnalysis (bs, sig, _) =
   if errs
      then Result.Result diag Nothing
      else Result.Result [] $ Just (bs, ExtSign newSig declaredSyms, formulae)
   where Diagn diag1 newSig = makeSig bs sig
         Diagn diag2 formulae = makeFormulas bs newSig
         declaredSyms = Set.map Symbol
                         $ Set.difference (getSymbols newSig) (getSymbols sig)
         diag = diag1 ++ diag2
         errs = Result.hasErrors diag

-- SIGNATURES
-- make a new signature out of a basic spec and an input signature
makeSig :: BASIC_SPEC -> Sign -> DIAGN Sign
makeSig (Basic_spec items) sig = addItemsToSig items sig

-- adds a list of annotated basic items to an input signature
addItemsToSig :: [Anno.Annoted BASIC_ITEM] -> Sign -> DIAGN Sign
addItemsToSig [] sig = Diagn [] sig
addItemsToSig (i:is) sig =
   case i of
        (Anno.Annoted (Axiom_item _) _ _ _) -> addItemsToSig is sig
        (Anno.Annoted (Decl_item d) _ _ _) ->
             if (Result.hasErrors diag)
                then Diagn diag sig
                else addItemsToSig is newSig
             where Diagn diag newSig = addDeclToSig d sig

-- adds a declaration to an existing signature
addDeclToSig :: DECL -> Sign -> DIAGN Sign
addDeclToSig dec sig = if valid
                          then Diagn [] $ addSymbolDecl dec sig
                          else Diagn diag sig
                       where Diagn diag valid = isValidDecl dec sig emptyContext

-- FORMULAS
-- make a list of formulas for the given signature out of a basic spec
makeFormulas :: BASIC_SPEC -> Sign -> DIAGN [Anno.Named FORMULA]
makeFormulas (Basic_spec items) sig = makeFormulasFromItems items 0 sig

-- make a list of named formulas out of a list of annotated items
makeFormulasFromItems :: [Anno.Annoted BASIC_ITEM] -> Int
                         -> Sign -> DIAGN [Anno.Named FORMULA]
makeFormulasFromItems [] _ _ = Diagn [] []
makeFormulasFromItems (i:is) num sig =
    case i of
         (Anno.Annoted (Decl_item _) _ _ _) -> makeFormulasFromItems is num sig
         (Anno.Annoted (Axiom_item a) _ _ annos) ->
           case fM of
                Just f ->
                   let Diagn diagL fs = makeFormulasFromItems is newNum sig
                       in Diagn diagL (f:fs)
                Nothing ->
                   let Diagn diagL fs = makeFormulasFromItems is num sig
                       in Diagn (diag ++ diagL) fs
           where Result.Result diag fM = makeNamedFormula a nam annos sig
                 label = Anno.getRLabel i
                 nam = if (label == "") then "Ax_" ++ show num else label
                 newNum = if (label == "") then num + 1 else num

-- make a named formula
makeNamedFormula :: FORMULA -> String -> [Anno.Annotation]
                    -> Sign -> Result.Result (Anno.Named FORMULA)
makeNamedFormula f nam annos sig =
    if valid
       then Result.Result [] $ Just $ namedF
       else Result.Result diag Nothing
    where Diagn diag valid = isValidFormula f sig emptyContext
          namedF = (Anno.makeNamed nam f) {Anno.isAxiom = not isTheorem}
          isImplies = or $ map Anno.isImplies annos
          isImplied = or $ map Anno.isImplied annos
          isTheorem = isImplies || isImplied

-- determines whether a formula is valid w.r.t. a signature and a context
isValidFormula :: FORMULA -> Sign -> CONTEXT -> DIAGN Bool
isValidFormula T _ _ = Diagn [] True
isValidFormula F _ _ = Diagn [] True
isValidFormula (Pred t) sig cont = hasType t Form sig cont
isValidFormula (Equality term1 term2) sig cont =
    case type1M of
         Nothing -> Diagn diag1 False
         Just type1 -> case type1 of
                            Univ _ -> hasType term2 type1 sig cont
                            _ -> Diagn [noDiscourseTermError term1 type1 cont]
                                       False
    where Result.Result diag1 type1M = getTermType term1 sig cont
isValidFormula (Negation f) sig cont = isValidFormula f sig cont
isValidFormula (Conjunction fs) sig cont =
   andD $ map (\f -> isValidFormula f sig cont) fs
isValidFormula (Disjunction fs) sig cont =
   andD $ map (\f -> isValidFormula f sig cont) fs
isValidFormula (Implication f g) sig cont =
   andD [isValidFormula f sig cont, isValidFormula g sig cont]
isValidFormula (Equivalence f g) sig cont =
   andD [isValidFormula f sig cont, isValidFormula g sig cont]
isValidFormula (Forall [] f) sig cont = isValidFormula f sig cont
isValidFormula (Forall (d:ds) f) sig cont =
   andD [validDecl, validFormula]
   where validDecl = isValidVarDecl d sig cont
         validFormula = isValidFormula (Forall ds f) sig (addVarDecl d cont)
isValidFormula (Exists [] f) sig cont = isValidFormula f sig cont
isValidFormula (Exists (d:ds) f) sig cont =
   andD [validDecl, validFormula]
   where validDecl = isValidVarDecl d sig cont
         validFormula = isValidFormula (Exists ds f) sig (addVarDecl d cont)

-- SYMBOL LIST AND MAP ANALYSIS
-- creates a symbol map out of a list of symbol map items
symbMapAnalysis :: [SYMB_MAP_ITEMS] -> Result.Result (Map.Map Symbol Symbol)
symbMapAnalysis xs = Result.Result []
     $ Just $ foldl (\ m x -> Map.union m (makeSymbMap x)) Map.empty xs

-- creates a symbol map out of symbol map items
makeSymbMap :: SYMB_MAP_ITEMS -> Map.Map Symbol Symbol
makeSymbMap (Symb_map_items xs) =
   foldl (\ m x -> case x of
                        Symb s -> Map.insert (Symbol s) (Symbol s) m
                        Symb_map s1 s2 -> Map.insert (Symbol s1) (Symbol s2) m
         )
         Map.empty
         xs

-- creates a symbol list out of a list of symbol items
symbAnalysis :: [SYMB_ITEMS] -> Result.Result [Symbol]
symbAnalysis xs = Result.Result [] $ Just $ concat $ map makeSymbols xs

-- creates a symbol list out of symbol item
makeSymbols :: SYMB_ITEMS -> [Symbol]
makeSymbols (Symb_items symbs) = map Symbol symbs

-- ERROR MESSAGES
noDiscourseTermError :: TERM -> TYPE -> CONTEXT -> Result.Diagnosis
noDiscourseTermError term t cont =
  Result.Diag
    { Result.diagKind = Result.Error
    , Result.diagString = "Term " ++ (show $ pretty term)
                          ++ " has the non-discourse type " ++ (show $ pretty t)
                          ++ " in the context " ++ (show $ pretty cont)
                          ++ " and hence cannot be used in an equality."
    , Result.diagPos = nullRange
    }
