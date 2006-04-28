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
import Common.PPUtils
import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.Fold

instance (Pretty b, Pretty s, Pretty f) => Pretty (BASIC_SPEC b s f) where
    pretty = printBASIC_SPEC pretty pretty pretty

printBASIC_SPEC :: (b -> Doc) -> (s -> Doc) -> (f -> Doc)
                -> BASIC_SPEC b s f -> Doc
printBASIC_SPEC fB fS fF (Basic_spec l) = case l of
    [] -> specBraces empty
    _ -> vcat $ map (printAnnoted ( printBASIC_ITEMS fB fS fF)) l

instance (Pretty b, Pretty s, Pretty f) => Pretty (BASIC_ITEMS b s f) where
    pretty = printBASIC_ITEMS pretty pretty pretty

printBASIC_ITEMS :: (b -> Doc) -> (s -> Doc) -> (f -> Doc)
                 -> BASIC_ITEMS b s f -> Doc
printBASIC_ITEMS fB fS fF sis = case sis of
    Sig_items s -> printSIG_ITEMS fS fF s
    Free_datatype l _ -> keyword freeS <+> keyword (typeS ++ pluralS l) <+>
         semiAnnos printDATATYPE_DECL l
    Sort_gen l _ -> case l of
         [Annoted (Datatype_items l' _) _ _ _] -> keyword generatedS <+>
                 keyword (typeS ++ pluralS l') <+>
                  semiAnnos printDATATYPE_DECL l'
         _ -> keyword generatedS <+> (specBraces $ vcat $ map
              (printAnnoted ((if isSingle l then rmTopKey else id) .
                     printSIG_ITEMS fS fF)) l)
    Var_items l _ -> keyword (varS ++ pluralS l) <+>
                           fsep (punctuate semi $ map printVarDecl l)
    Local_var_axioms l f _  ->
            fsep [fsep $ forallDoc : punctuate semi (map printVarDecl l)
                 , printAnnotedBulletFormulas fF f]
    Axiom_items f _ -> printAnnotedBulletFormulas fF f
    Ext_BASIC_ITEMS b -> fB b

printAnnotedBulletFormulas :: (f -> Doc) -> [Annoted (FORMULA f)] -> Doc
printAnnotedBulletFormulas fF = vcat . map
    (printAnnoted $ addBullet . printFormula fF)

instance (Pretty s, Pretty f) => Pretty (SIG_ITEMS s f) where
    pretty = printSIG_ITEMS pretty pretty

printSIG_ITEMS :: (s -> Doc) -> (f -> Doc) -> SIG_ITEMS s f -> Doc
printSIG_ITEMS fS fF sis = case sis of
    Sort_items l _ -> topKey (sortS ++ pluralS l) <+>
         semiAnnos (printSortItem fF) l
    Op_items l _  -> topKey (opS ++ pluralS l) <+>
             semiAnnos (printOpItem fF) l
    Pred_items l _ -> topKey (predS ++ pluralS l) <+>
             semiAnnos (printPredItem fF) l
    Datatype_items l _ -> topKey (typeS ++ pluralS l) <+>
             semiAnnos printDATATYPE_DECL l
    Ext_SIG_ITEMS s -> fS s

printDATATYPE_DECL :: DATATYPE_DECL ->Doc
printDATATYPE_DECL (Datatype_decl s a _) = case a of
    [] -> idDoc s
    _  -> fsep [idDoc s, defn, sep $ punctuate (space <> bar) $
                      map (printAnnoted printALTERNATIVE) a]

instance Pretty DATATYPE_DECL where
    pretty = printDATATYPE_DECL

printCOMPONENTS :: COMPONENTS ->Doc
printCOMPONENTS c = case c of
    Cons_select k l s _ -> fsep $ punctuate comma (map idDoc l)
           ++ [case k of
           Total -> colon
           Partial -> colon <> text "?", idDoc s]
    Sort s -> idDoc s

instance Pretty COMPONENTS  where
    pretty = printCOMPONENTS

printALTERNATIVE :: ALTERNATIVE ->Doc
printALTERNATIVE a = case a of
  Alt_construct k n l _ -> case l of
    [] -> idDoc n
    _ ->  idDoc n <>
       parens ( sep $ punctuate semi $ map printCOMPONENTS l)
       <> case k of
               Total -> empty
               Partial -> text "?"
  Subsorts l _ -> fsep $ text (sortS ++ if isSingle l then "" else "s")
                            : punctuate comma (map idDoc l)

instance Pretty ALTERNATIVE where
    pretty = printALTERNATIVE

printSortItem :: (f -> Doc) -> SORT_ITEM f -> Doc
printSortItem mf si = case si of
    Sort_decl sl _ -> fsep $ punctuate comma $ map idDoc sl
    Subsort_decl sl sup _ -> fsep $ (punctuate comma $ map idDoc sl)
                                     ++ [less, idDoc sup]
    Subsort_defn s v sup af _ -> fsep [idDoc s, equals,
              specBraces $ fsep [sidDoc v, colon, idDoc sup,
                             printAnnoted (addBullet . printFormula mf) af]]
    Iso_decl sl _ -> fsep $ punctuate (space <> equals) $ map idDoc sl

instance Pretty f => Pretty (SORT_ITEM f) where
    pretty = printSortItem pretty

addBullet :: Doc -> Doc
addBullet = (bullet <+>)

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

instance Pretty f => Pretty (PRED_ITEM f) where
    pretty = printPredItem pretty


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

instance Pretty f => Pretty (OP_ITEM f) where
    pretty = printOpItem pretty


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
        parens $ fsep [text predS, idDoc i, colon <+> printPredType t]

instance Pretty PRED_SYMB where
    pretty = printPredSymb

instance Pretty SYMB_ITEMS where
    pretty = printSymbItems

printSymbItems :: SYMB_ITEMS -> Doc
printSymbItems (Symb_items k l _) =
    print_kind_text k l <+> (fsep $ punctuate comma $ map printSymb l)

instance Pretty SYMB where
    pretty = printSymb

printSymb :: SYMB -> Doc
printSymb s = case s of
    Symb_id i -> idDoc i
    Qual_id i t _ -> fsep [idDoc i, colon <> printType t]

instance Pretty TYPE where
    pretty = printType

printType :: TYPE -> Doc
printType t = case t of
    O_type ot -> printOpType ot
    P_type pt -> space <> printPredType pt
    A_type s  -> idDoc s

print_kind_text :: SYMB_KIND -> [a] -> Doc
print_kind_text k l = case k of
    Implicit -> empty
    _ -> keyword (pluralS_symb_list k l)

pluralS_symb_list :: SYMB_KIND -> [a] -> String
pluralS_symb_list k l = (case k of
    Implicit -> error "pluralS_symb_list"
    Sorts_kind -> sortS
    Ops_kind   -> opS
    Preds_kind -> predS) ++ (if isSingle l then "" else "s")

instance Pretty SYMB_OR_MAP where
    pretty = printSymbOrMap

printSymbOrMap :: SYMB_OR_MAP -> Doc
printSymbOrMap som = case som of
    Symb s -> printSymb s
    Symb_map s t _ -> fsep [printSymb s, mapsto <+> printSymb t]

instance Pretty SYMB_KIND where
    pretty = printSymbKind

printSymbKind :: SYMB_KIND -> Doc
printSymbKind sk = print_kind_text sk [()]

instance Pretty SYMB_MAP_ITEMS where
    pretty = printSymbMapItems

printSymbMapItems :: SYMB_MAP_ITEMS -> Doc
printSymbMapItems (Symb_map_items k l _) =
    print_kind_text k l <+> (fsep $ punctuate comma $ map printSymbOrMap l)

printRecord :: (f -> Doc) -> Record f Doc Doc
printRecord mf = Record
    { foldQuantification = \ _ q l r _ ->
          fsep $ printQuant q : punctuate semi (map printVarDecl l)
                                ++ [addBullet r]
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

---- instances of ListCheck for various data types of AS_Basic_CASL ---

instance ListCheck (SORT_ITEM f) where
    innerList (Sort_decl l _) = innerList l
    innerList (Subsort_decl l _ _) = innerList l
    innerList (Subsort_defn _ _ _ _ _) = [()]
    innerList (Iso_decl _ _) = [()]

instance ListCheck (OP_ITEM f) where
    innerList (Op_decl l _ _ _) = innerList l
    innerList (Op_defn _ _ _ _) = [()]

instance ListCheck (PRED_ITEM f) where
    innerList (Pred_decl l _ _) = innerList l
    innerList (Pred_defn _ _ _ _) = [()]

instance ListCheck DATATYPE_DECL where
    innerList (Datatype_decl _ _ _) = [()]

instance ListCheck VAR_DECL where
    innerList (Var_decl l _ _) = innerList l

-----------------------------------------------------------------------------
