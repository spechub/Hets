{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

pretty printing data types of 'BASIC_SPEC'
-}

module CASL.ToDoc where

import Common.Id
import Common.Keywords
import Common.Doc

import CASL.AS_Basic_CASL
import CASL.Fold

printSortItem :: (f -> Doc) -> SORT_ITEM f -> Doc
printSortItem mf si = case si of
    Sort_decl sl _ -> fsep $ punctuate comma $ map idDoc sl
    Subsort_decl sl sup _ -> fsep $ (punctuate comma $ map idDoc sl)
                                     ++ [less, idDoc sup] 
    Subsort_defn s v sup af _ -> fsep [idDoc s, equals, 
              specBraces $ fsep [sidDoc v, colon, idDoc sup, bullet,
                             printAnnoted (printFormula mf) af]]
    Iso_decl sl _ -> fsep $ punctuate (space <> equals) $ map idDoc sl

sidDoc :: Token -> Doc
sidDoc = idDoc . simpleIdToId

printQuant :: QUANTIFIER -> Doc
printQuant q = case q of
    Universal -> forallDoc
    Existential -> exists
    Unique_existential -> unique

printSortedVars :: [VAR] -> SORT -> Doc
printSortedVars l s =
    fsep $ (punctuate comma $ map sidDoc l) ++ [colon, idDoc s]

printVarDecl :: VAR_DECL -> Doc
printVarDecl (Var_decl l s _) = printSortedVars l s

printArgDecl :: ARG_DECL -> Doc
printArgDecl (Arg_decl l s _) = printSortedVars l s

printArgDecls :: [ARG_DECL] -> Doc
printArgDecls = parens . fsep . punctuate semi . map printArgDecl

printPredHead :: PRED_HEAD -> Doc
printPredHead (Pred_head l _) = printArgDecls l

printPredItem :: (f -> Doc) -> PRED_ITEM f -> Doc
printPredItem mf p = case p of
    Pred_decl l t _ -> fsep $ (punctuate comma $ map idDoc l)
                       ++ [colon, printPredType t]
    Pred_defn i h f _ ->
        fcat [idDoc i, printPredHead h <> space, equiv <> space,
              printAnnoted (printFormula mf) f]

printAttr :: (f -> Doc) -> OP_ATTR f -> Doc
printAttr mf a = case a of
    Assoc_op_attr -> text assocS
    Comm_op_attr -> text commS
    Idem_op_attr -> text idemS
    Unit_op_attr t -> text unitS <+> printTerm mf t

instance Pretty f => Pretty (OP_ATTR f) where
    pretty = printAttr pretty

printOpHead :: OP_HEAD -> Doc
printOpHead (Op_head k l r _) =
    fcat $ (if null l then [] else [printArgDecls l <> space]) ++
         [ (case k of
             Total -> colon
             Partial -> idDoc $ mkId [mkSimpleId ":?"]) <> space
         , idDoc r]

instance Pretty OP_HEAD where
    pretty = printOpHead

printOpItem :: (f -> Doc) -> OP_ITEM f -> Doc
printOpItem mf p = case p of
    Op_decl l t a _ -> fsep $ (punctuate comma $ map idDoc l)
        ++ [colon <> (if null a then id else (<> comma))(printOpType t)]
        ++ punctuate comma (map (printAttr mf) a)
    Op_defn i h@(Op_head _ l _ _) t _ ->
        fcat [(if null l then (<> space) else id) $ idDoc i
             , printOpHead h <> space, equals <> space
             , printAnnoted (printTerm mf) t]

instance Pretty VAR_DECL where
    pretty = printVarDecl

printOpType :: OP_TYPE -> Doc
printOpType (Op_type p l r _) =
    case l of
      [] -> case p of
          Partial -> text quMark <+> idDoc r
          Total -> space <> idDoc r
      _ -> space <> fsep 
             (punctuate (space <> cross) (map idDoc l)
             ++ [case p of
                Partial -> pfun
                Total -> funArrow,
                 idDoc r])

instance Pretty OP_TYPE where
    pretty = printOpType

printOpSymb :: OP_SYMB -> Doc
printOpSymb o = case o of
    Op_name i -> idDoc i
    Qual_op_name i t _ -> fsep [text opS, idDoc i, colon <> printOpType t]

instance Pretty OP_SYMB where
    pretty = printOpSymb

printPredType :: PRED_TYPE -> Doc
printPredType (Pred_type l _) = case l of
    [] -> parens empty
    _ -> fsep $ punctuate (space <> cross) $ map idDoc l

instance Pretty PRED_TYPE where
    pretty = printPredType

printPredSymb :: PRED_SYMB -> Doc
printPredSymb p = case p of
    Pred_name i -> idDoc i
    Qual_pred_name i t _ ->
        parens $ fsep [text predS, idDoc i, colon, printPredType t]

instance Pretty PRED_SYMB where
    pretty = printPredSymb

printRecord :: (f -> Doc) -> Record f Doc Doc
printRecord mf = Record
    { foldQuantification = \ _ q l r _ ->
          fsep $ printQuant q : punctuate semi (map printVarDecl l)
                                ++ [bullet, r]
    , foldConjunction = \ (Conjunction ol _) l _ ->
          fsep $ punctuate (space <> andDoc) $ zipWith mkJunctDoc ol l
    , foldDisjunction = \ (Disjunction ol _) l _ ->
          fsep $ punctuate (space <> orDoc) $ zipWith mkJunctDoc ol l
    , foldImplication = \ (Implication oL oR b _) l r _ _ ->
          let nl = if isAnyImpl oL then parens l else l
              nr = if isImpl b oR then parens r else r
          in if b then fsep [nl, implies, nr]
             else fsep [nr, text ifS, nl]
    , foldEquivalence = \ (Equivalence oL oR _) l r _ ->
          fsep [mkEquivDoc oL l, equiv, mkEquivDoc oR r]
    , foldNegation = \ (Negation o _) r _ -> hsep [notDoc, mkJunctDoc o r]
    , foldTrue_atom = \ _ _ -> text trueS
    , foldFalse_atom = \ _ _ -> text falseS
    , foldPredication = \ _ p l _ -> case p of
          Pred_name i -> idApplDoc i l
          Qual_pred_name _ _ _ -> if null l then printPredSymb p else
              fcat [printPredSymb p, parens $ fsep $ punctuate comma l]
    , foldDefinedness = \ _ r _ -> hsep [text defS, r]
    , foldExistl_equation = \ _ l r _ -> fsep [l, exequal, r]
    , foldStrong_equation = \ _ l r _ -> fsep [l, equals, r]
    , foldMembership = \ _ r t _ -> fsep [r, inDoc, idDoc t]
    , foldMixfix_formula = \ _ r -> r
    , foldSort_gen_ax = \ (Sort_gen_ax constrs _) _ _ ->
        let (sorts, ops, sortMap) = recover_Sort_gen_ax constrs
            printSortMap (s1, s2) = fsep [idDoc s1, mapsto, idDoc s2]
        in text generatedS <> specBraces(
                fsep (text sortS : punctuate comma (map idDoc sorts))
                <> semi <+>
                fsep (punctuate semi (map printOpSymb ops))
                <> if null sortMap then empty else
                   space <> text withS
                    <+> fsep (punctuate comma (map printSortMap sortMap)))
    , foldExtFORMULA = \ _ f -> mf f
    , foldSimpleId = \ _ -> sidDoc
    , foldQual_var = \ _ v s _ ->
          parens $ fsep [text varS, sidDoc v, colon, idDoc s]
    , foldApplication = \ _ o l _ -> case o of
          Op_name i -> idApplDoc i l
          Qual_op_name _ _ _ -> let d = parens $ printOpSymb o in
              if null l then d else fcat [d, parens $ fsep $ punctuate comma l]
    , foldSorted_term = \ _ r t _ -> fsep[idApplDoc typeId [r], idDoc t]
    , foldCast = \ _ r t _ ->
          fsep[idApplDoc (mkId [placeTok, mkSimpleId asS]) [r], idDoc t]
    , foldConditional = \ (Conditional ol _ _ _) l f r _ ->
          fsep [if isCond ol then parens l else l,
                text whenS, f, text elseS, r]
    , foldMixfix_qual_pred = \ _ p -> printPredSymb p
    , foldMixfix_term = \ (Mixfix_term ol) l -> case ol of
          [_, Mixfix_parenthesized _ _] -> fcat l
          _ -> fsep l
    , foldMixfix_token = \ _ -> sidDoc
    , foldMixfix_sorted_term = \ _ s _ -> colon <+> idDoc s
    , foldMixfix_cast = \ _ s _ -> text asS <+> idDoc s
    , foldMixfix_parenthesized = \ _ l _ -> parens $ fsep $ punctuate comma l
    , foldMixfix_bracketed = \ _ l _ -> brackets $ fsep $ punctuate comma l
    , foldMixfix_braced = \ _ l _ -> specBraces $ fsep $ punctuate comma l
    }

printFormula :: (f -> Doc) -> FORMULA f -> Doc
printFormula mf = foldFormula $ printRecord mf

instance Pretty f => Pretty (FORMULA f) where
    pretty = printFormula pretty

printTerm :: (f -> Doc) -> TERM f -> Doc
printTerm mf = foldTerm $ printRecord mf

instance Pretty f => Pretty (TERM f) where
    pretty = printTerm pretty

isQuant, isEquiv, isAnyImpl, isJunct :: FORMULA f -> Bool
isQuant f = case f of
    Quantification _ _ _ _ -> True
    _ -> False

isEquiv f = case f of
    Equivalence _ _ _ -> True
    _ -> isQuant f

isAnyImpl f = isImpl True f || isImpl False f

isJunct f = case f of
    Conjunction _ _ -> True
    Disjunction _ _ -> True
    _ -> isAnyImpl f

mkJunctDoc :: FORMULA f -> Doc -> Doc
mkJunctDoc f = if isJunct f then parens else id

mkEquivDoc :: FORMULA f -> Doc -> Doc
mkEquivDoc f = if isEquiv f then parens else id

isImpl :: Bool -> FORMULA f -> Bool
isImpl a f = case f of
    Implication _ _ b _ -> a /= b
    _ -> isEquiv f

isCond :: TERM f -> Bool
isCond t = case t of
    Conditional _ _ _ _ -> True
    _ -> False
