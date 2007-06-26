{- |
Module      :  $Header$
Description :  Pretty printing for SPASS signatures in TPTP syntax.
Copyright   :  (c) Rene Wagner, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  unknown

Pretty printing for SoftFOL signatures in TPTP syntax.
   Refer to <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
   for the TPTP syntax documentation.

-}

module SoftFOL.PrintTPTP where

import Maybe

import Common.AS_Annotation
import Common.Doc

import Control.Exception

import SoftFOL.Sign
import SoftFOL.Conversions

-- | This type class allows pretty printing in TPTP syntax of instantiated data
--   types
class PrintTPTP a where
    printTPTP :: a -> Doc

{- |
  Helper function. Generates a separating comment line.
-}
separator :: String
separator = '%' : replicate 75 '-'

{- |
  Helper function. Generates a comma separated list of SoftFOL Terms as a Doc.
-}
printCommaSeparated :: [SPTerm] -> Doc
printCommaSeparated = hcat . punctuate comma . map printTPTP

instance PrintTPTP Sign where
    printTPTP = printTPTP . signToSPLogicalPart

{- |
  Creates a Doc from a SoftFOL Problem.
-}
instance PrintTPTP SPProblem where
    printTPTP p = text separator
      $+$ text "% Problem" <+> colon <+> text (identifier p)
      $+$ printTPTP (description p)
      $+$ vcat (map printTPTP $ settings p)
      $+$ text separator
      $+$ printTPTP (logicalPart p)

{- |
  Creates a Doc from a SoftFOL Logical Part.
-}
instance PrintTPTP SPLogicalPart where
    printTPTP lp =
      let validDeclarations = filter (\ decl -> case decl of
              SPSubsortDecl{}    -> True
              SPTermDecl{}       -> True
              SPSimpleTermDecl _ -> True
              _                  -> False) $ declarationList lp
      in vcat (map (\ (decl, i) ->
                    text "fof" <>
                    parens (text ("declaration" ++ show i) <> comma <>
                    printTPTP SPOriginAxioms <> comma
                    $+$ parens (printTPTP decl)) <> dot)
                $ zip validDeclarations [(0::Int)..])
         $+$ vcat (map printTPTP $ formulaLists lp)

{- |
 Creates a Doc from a SoftFOL Declaration.
 A subsort declaration will be rewritten as a special SPQuantTerm.
-}
instance PrintTPTP SPDeclaration where
    printTPTP decl = case decl of
      SPSubsortDecl{sortSymA= sortA, sortSymB= sortB}
        -> let subsortVar = spTerms $ genVarList sortA [sortB]
           in
           printTPTP SPQuantTerm{
                       quantSym=SPForall,
                       variableList=subsortVar,
                       qFormula=SPComplexTerm{
                                  symbol=SPImplies,
                                  arguments=[SPComplexTerm{
                                               symbol=SPCustomSymbol sortA,
                                               arguments=subsortVar},
                                             SPComplexTerm{
                                               symbol=SPCustomSymbol sortB,
                                               arguments=subsortVar}]
                                }}
      SPTermDecl{termDeclTermList= tlist, termDeclTerm= tt}
        -> printTPTP SPQuantTerm{
                       quantSym=SPForall,
                       variableList=tlist,
                       qFormula=tt}
      SPSimpleTermDecl stsym -> printTPTP stsym
      pd@(SPPredDecl {}) -> maybe empty printTPTP $ predDecl2Term pd
      _ -> empty 

{- |
  Creates a Doc from a SoftFOL Formula List.
-}
instance PrintTPTP SPFormulaList where
    printTPTP l = vcat $ map (printFormula $ originType l) $ formulae l

{- |
  Creates a Doc from a SoftFOL Origin Type.
-}
instance PrintTPTP SPOriginType where
    printTPTP t = text $ case t of
        SPOriginAxioms      -> "axiom"
        SPOriginConjectures -> "conjecture"

{- |
  Creates a Doc from a SoftFOL Formula. Needed since SPFormula is just a
  'type SPFormula = Named SPTerm' and thus instanciating PrintTPTP is not
  possible.
-}
printFormula :: SPOriginType -> SPFormula -> Doc
-- printFormula ot f = printFormulaText ot (senName f) (sentence f)
printFormula ot f =
    text "fof" <> parens (text (senName f) <> comma <> printTPTP ot <> comma
                          $+$ parens (printTPTP $ sentence f)) <> dot

{- |
  Creates a Doc from a SoftFOL Term.
-}
instance PrintTPTP SPTerm where
    printTPTP t = case t of
      SPQuantTerm{quantSym= qsym, variableList= tlist, qFormula= tt}
        -> printTPTP qsym
           <+> brackets (printCommaSeparated $ getVariables tlist)
           <+> colon
           -- either all variables are simple terms
           <+> if (filter isSimpleTerm tlist == tlist) then printTPTP tt
               -- or there are none simple terms
               else assert (null $ filter isSimpleTerm tlist)
          -- construct premiss for implication out of variableList (Forall)
          -- construct conjunction out of variableList (Exists)
                           printTermList (cond qsym) [SPComplexTerm{
                                                      symbol=SPAnd,
                                                      arguments=tlist}, tt]
      SPSimpleTerm stsym -> printTPTP stsym
      SPComplexTerm{symbol= ctsym, arguments= args}
        -> if null args
           then printTPTP ctsym
           else printTermList ctsym args
      where
        isSimpleTerm tm = case tm of
            SPSimpleTerm _ -> True
            _              -> False

        -- check that every list entry is simple term
        getSimpleVars = foldr (\v vl -> assert (isSimpleTerm v) $ v:vl) []
        getVariables tl = if null $ filter isSimpleTerm tl
                          then foldr (\co col -> (getSimpleVars $
                                                  arguments co)++col)
                                     [] tl
                          else getSimpleVars tl

        cond qsy = case qsy of
                     SPForall -> SPImplies
                     SPExists -> SPAnd
                     _ -> error "SoftFOL.PrintTPTP: unknown quantifier symbol"

{- |
  Creates a Doc from a list of SoftFOL Terms connected by a SoftFOL Symbol.
-}
printTermList :: SPSymbol -> [SPTerm] -> Doc
printTermList symb terms = case symb of
    SPEqual            -> assert (length terms == 2) $ associate SPEqual
    SPTrue             -> assert (length terms == 0) $ associate SPTrue
    SPFalse            -> assert (length terms == 0) $ associate SPFalse
    -- variable number of terms for or/and
    SPOr               -> assert (length terms >= 0) $ associate SPOr
    SPAnd              -> assert (length terms >= 0) $ associate SPAnd
    -- only one term can be negated
    SPNot              -> assert (length terms == 1) $ applicate SPNot
    SPImplies          -> assert (length terms == 2) $ associate SPImplies
    SPImplied          -> assert (length terms == 2) $ associate SPImplied
    SPEquiv            -> assert (length terms == 2) $ associate SPEquiv
    SPCustomSymbol cst -> applicate $ SPCustomSymbol cst
    where
      associate sb = case terms of
        []  -> empty
        [x] -> printTPTP x
        _   -> parens $ vcat $ punctuate (space <> printTPTP sb)
                      $ map printTPTP terms
      applicate sb =
        if null terms then printTPTP sb
        else printTPTP sb <> parens (printCommaSeparated terms)

{- |
  Creates a Doc from a SoftFOL Quantifier Symbol.
-}
instance PrintTPTP SPQuantSym where
    printTPTP qs = text $ case qs of
        SPForall             -> "!"
        SPExists             -> "?"
        SPCustomQuantSym cst -> cst

{- |
  Creates a Doc from a SoftFOL Symbol.
-}
instance PrintTPTP SPSymbol where
    printTPTP s = text $ case s of
        SPEqual            -> "="
        SPTrue             -> "$true"
        SPFalse            -> "$false"
        SPOr               -> "|"
        SPAnd              -> "&"
        SPNot              -> "~"
        SPImplies          -> "=>"
        SPImplied          -> "<="
        SPEquiv            -> "<=>"
        SPCustomSymbol cst -> cst

{- |
  Creates a Doc from a SoftFOL description.
-}
instance PrintTPTP SPDescription where
    printTPTP d = spCommentText "Name   " (name d)
      $+$ spCommentText "Author " (author d)
      $+$ maybe empty (spCommentText "Version") (version d)
      $+$ maybe empty (spCommentText "Logic  ") (logic d)
      $+$ text "% Status " <+> colon <+> printTPTP (status d)
      $+$ spCommentText "Desc   " (desc d)
      $+$ maybe empty (spCommentText "Date   ") (date d)

{- |
  Helper function. Creates a formatted comment output for a description field.
  On left side will be displayed the field's name, on right side its content.
-}
spCommentText :: String -> String -> Doc
spCommentText fieldName fieldDesc =
    hsep [text "%", text fieldName, colon, text fieldDesc]

{- |
  Creates a Doc from an 'SPLogState'.
-}
instance PrintTPTP SPLogState where
    printTPTP s = text $ case s of
      SPStateSatisfiable   -> "satisfiable"
      SPStateUnsatisfiable -> "unsatisfiable"
      SPStateUnknown       -> "unknown"

instance PrintTPTP SPSetting where
    printTPTP (SPFlag sw v) =
      if (null sw) then
        hsep [text "% Option ", colon, text v]
      else
        hsep [text "% Option ", colon, text sw, comma, text v]
    printTPTP _ = 
        error "SPClauseRelation pretty printing not yet implemented"

