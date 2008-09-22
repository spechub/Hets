{- |
Module      :  $Header$
Description :  pretty printing data types of BASIC_SPEC
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

Pretty printing data types of 'BASIC_SPEC'
-}

module CASL.ToDoc
    ( printBASIC_SPEC
    , printFormula
    , printTerm
    , printTheoryFormula
    , pluralS
    , isJunct
    , ListCheck(..)
    , recoverType
    , printALTERNATIVE
    ) where

import Common.Id
import Common.Keywords
import Common.Doc
import Common.DocUtils
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

typeString :: SortsKind -> [Annoted DATATYPE_DECL] -> String
typeString sk l = (case sk of
    NonEmptySorts -> typeS
    PossiblyEmptySorts -> etypeS) ++ pluralS l

printBASIC_ITEMS :: (b -> Doc) -> (s -> Doc) -> (f -> Doc)
                 -> BASIC_ITEMS b s f -> Doc
printBASIC_ITEMS fB fS fF sis = case sis of
    Sig_items s -> printSIG_ITEMS fS fF s
    Free_datatype sk l _ -> sep [keyword freeS <+> keyword (typeString sk l),
                                 semiAnnos printDATATYPE_DECL l]
    Sort_gen l _ -> case l of
         [Annoted (Datatype_items sk l' _) _ las ras] ->
             (if null las then id else (printAnnotationList las $+$))
             $ (if null ras then id else ($+$ printAnnotationList ras))
             $ sep [keyword generatedS <+> keyword (typeString sk l'),
                    semiAnnos printDATATYPE_DECL l']
         _ -> sep [keyword generatedS, specBraces $ vcat $ map
              (printAnnoted $ printSIG_ITEMS fS fF) l]
    Var_items l _ -> topSigKey (varS ++ pluralS l) <+>
                           fsep (punctuate semi $ map printVarDecl l)
    Local_var_axioms l f _  ->
            fsep [fsep $ forallDoc : punctuate semi (map printVarDecl l)
                 , printAnnotedBulletFormulas fF f]
    Axiom_items f _ -> printAnnotedBulletFormulas fF f
    Ext_BASIC_ITEMS b -> fB b

printAnnotedBulletFormulas :: (f -> Doc) -> [Annoted (FORMULA f)] -> Doc
printAnnotedBulletFormulas fF l = vcat $ case l of
    [] -> []
    _ -> let pp = addBullet . printFormula fF in
         map (printAnnoted pp) (init l)
         ++ [printSemiAnno pp False $ last l] -- use True for HasCASL

instance (Pretty s, Pretty f) => Pretty (SIG_ITEMS s f) where
    pretty = printSIG_ITEMS pretty pretty

printSIG_ITEMS :: (s -> Doc) -> (f -> Doc) -> SIG_ITEMS s f -> Doc
printSIG_ITEMS fS fF sis = case sis of
    Sort_items sk l _ -> topSigKey ((case sk of
        NonEmptySorts -> sortS
        PossiblyEmptySorts -> esortS) ++ pluralS l) <+>
         semiAnnos (printSortItem fF) l
    Op_items l _  -> topSigKey (opS ++ pluralS l) <+>
        let pp = printOpItem fF in
        if null l then empty else if case item $ last l of
            Op_decl _ _ a@(_ : _) _ -> case last a of
                Unit_op_attr {} -> False  -- use True for HasCASL
                _ -> False
            Op_defn {} -> False  -- use True for HasCASL
            _ -> False
        then vcat $ map (printSemiAnno pp True) l else semiAnnos pp l
    Pred_items l _ -> topSigKey (predS ++ pluralS l) <+>
        let pp = printPredItem fF in
        if null l then empty else if case item $ last l of
            Pred_defn {} -> True
            _ -> False
        then vcat $ map (printSemiAnno pp True) l else semiAnnos pp l
    Datatype_items sk l _ -> topSigKey (typeString sk l) <+>
             semiAnnos printDATATYPE_DECL l
    Ext_SIG_ITEMS s -> fS s

printDATATYPE_DECL :: DATATYPE_DECL ->Doc
printDATATYPE_DECL (Datatype_decl s a r) =
    let pa = printAnnoted printALTERNATIVE in case a of
    [] -> printDATATYPE_DECL (Datatype_decl s [emptyAnno $ Subsorts [s] r] r)
    h : t  -> sep [idLabelDoc s, colon <> colon <> sep
                      ((equals <+> pa h) :
                       map ((bar <+>) . pa) t)]

instance Pretty DATATYPE_DECL where
    pretty = printDATATYPE_DECL

printCOMPONENTS :: COMPONENTS ->Doc
printCOMPONENTS c = case c of
    Cons_select k l s _ -> fsep $ punctuate comma (map idLabelDoc l)
           ++ [case k of
           Total -> colon
           Partial -> colon <> quMarkD, idDoc s]
    Sort s -> idDoc s

instance Pretty COMPONENTS  where
    pretty = printCOMPONENTS

printALTERNATIVE :: ALTERNATIVE ->Doc
printALTERNATIVE a = case a of
  Alt_construct k n l _ -> case l of
    [] -> idLabelDoc n
    _ -> idLabelDoc n <>
       parens ( sep $ punctuate semi $ map printCOMPONENTS l)
       <> case k of
               Total -> empty
               Partial -> quMarkD
  Subsorts l _ -> fsep $ text (sortS ++ pluralS l)
                            : punctuate comma (map idDoc l)

instance Pretty ALTERNATIVE where
    pretty = printALTERNATIVE

printSortItem :: (f -> Doc) -> SORT_ITEM f -> Doc
printSortItem mf si = case si of
    Sort_decl sl _ -> sepByCommas $ map idLabelDoc sl
    Subsort_decl sl sup _ -> fsep $ (punctuate comma $ map idDoc sl)
                                     ++ [less, idDoc sup]
    Subsort_defn s v sup af _ -> fsep [idLabelDoc s, equals,
              specBraces $ fsep [sidDoc v, colon <+> idDoc sup,
                             printAnnoted (addBullet . printFormula mf) af]]
    Iso_decl sl _ -> fsep $ punctuate (space <> equals) $ map idDoc sl

instance Pretty f => Pretty (SORT_ITEM f) where
    pretty = printSortItem pretty

printQuant :: QUANTIFIER -> Doc
printQuant q = case q of
    Universal -> forallDoc
    Existential -> exists
    Unique_existential -> unique

printSortedVars :: [VAR] -> SORT -> Doc
printSortedVars l s =
    fsep $ (punctuate comma $ map sidDoc l) ++ [colon <+> idDoc s]

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
    Pred_decl l t _ -> fsep $ (punctuate comma $ map idLabelDoc l)
                       ++ [colon <+> printPredType t]
    Pred_defn i h f _ ->
        sep[ cat [idLabelDoc i, printPredHead h]
           , equiv <+> printAnnoted (printFormula mf) f]

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
    sep $ (if null l then [] else [printArgDecls l]) ++
         [ (case k of
             Total -> colon
             Partial -> text colonQuMark) <+> idDoc r]

instance Pretty OP_HEAD where
    pretty = printOpHead

printOpItem :: (f -> Doc) -> OP_ITEM f -> Doc
printOpItem mf p = case p of
    Op_decl l t a _ -> fsep $ (punctuate comma $ map idLabelDoc l)
        ++ [colon <> (if null a then id else (<> comma))(printOpType t)]
        ++ punctuate comma (map (printAttr mf) a)
    Op_defn i h@(Op_head _ l _ _) t _ ->
        sep [ (if null l then sep else cat) [idLabelDoc i, printOpHead h]
            , equals <+> printAnnoted (printTerm mf) t]

instance Pretty f => Pretty (OP_ITEM f) where
    pretty = printOpItem pretty

instance Pretty VAR_DECL where
    pretty = printVarDecl

printOpType :: OP_TYPE -> Doc
printOpType (Op_type p l r _) =
    case l of
      [] -> case p of
          Partial -> quMarkD <+> idDoc r
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
    print_kind_text k l <+> sepByCommas (map printSymb l)

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
    A_type s  -> space <> idDoc s

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
    print_kind_text k l <+> sepByCommas (map printSymbOrMap l)

printRecord :: (f -> Doc) -> Record f Doc Doc
printRecord mf = Record
    { foldQuantification = \ _ q l r _ ->
          fsep $ printQuant q : punctuate semi (map printVarDecl l)
                                ++ [addBullet r]
    , foldConjunction = \ (Conjunction ol _) l _ -> case ol of
          [] -> text trueS
          _ -> fsep $ prepPunctuate (andDoc <> space)
               $ zipWith (mkJunctDoc True) (init ol) (init l) ++
                 [mkJunctDoc False (last ol) (last l)]
    , foldDisjunction = \ (Disjunction ol _) l _ -> case ol of
          [] -> text falseS
          _ -> fsep $ prepPunctuate (orDoc <> space)
               $ zipWith (mkJunctDoc True) (init ol) (init l) ++
                 [mkJunctDoc False (last ol) (last l)]
    , foldImplication = \ (Implication oL oR b _) l r _ _ ->
          let nl = if isAnyImpl oL || b && isQuant oL
                   then parens l else l
              nr = if isImpl b oR || not b && isQuant oR
                   then parens r else r
          in if b then sep [nl, hsep [implies, nr]]
             else sep [nr, hsep [text ifS, nl]]
    , foldEquivalence = \ (Equivalence oL oR _) l r _ ->
          sep [if isQuant oL then parens l else
                   mkEquivDoc oL l, hsep [equiv, mkEquivDoc oR r]]
    , foldNegation = \ (Negation o _) r _ ->
          hsep [notDoc, mkJunctDoc False o r]
    , foldTrue_atom = \ _ _ -> text trueS
    , foldFalse_atom = \ _ _ -> text falseS
    , foldPredication = \ (Predication _ ol _) p l _ -> case p of
          Pred_name i -> predIdApplDoc i $ zipConds ol l
          Qual_pred_name _ _ _ -> if null l then printPredSymb p else
              fcat [printPredSymb p, parens $ sepByCommas l]
    , foldDefinedness = \ _ r _ -> hsep [text defS, r]
    , foldExistl_equation = \ _ l r _ -> sep [l, hsep[exequal, r]]
    , foldStrong_equation = \ _ l r _ -> sep [l, hsep [equals, r]]
    , foldMembership = \ _ r t _ -> fsep [r, inDoc, idDoc t]
    , foldMixfix_formula = \ _ r -> r
    , foldSort_gen_ax = \ (Sort_gen_ax constrs b) _ _ ->
        let l = recoverType constrs
            genAx = sep [ keyword generatedS <+> keyword (typeS ++ pluralS l)
                        , semiAnnos printDATATYPE_DECL l]
        in if b then text "%% free" $+$ genAx else genAx
    , foldExtFORMULA = \ _ f -> mf f
    , foldQual_var = \ _ v s _ ->
          parens $ fsep [text varS, sidDoc v, colon <+> idDoc s]
    , foldApplication = \ (Application _ ol _) o l _ -> case o of
          Op_name i -> idApplDoc i $ zipConds ol l
          Qual_op_name _ _ _ -> let d = parens $ printOpSymb o in
              if null l then d else fcat [d, parens $ sepByCommas l]
    , foldSorted_term = \ _ r t _ -> fsep[idApplDoc typeId [r], idDoc t]
    , foldCast = \ _ r t _ ->
          fsep[idApplDoc (mkId [placeTok, mkSimpleId asS]) [r], idDoc t]
    , foldConditional = \ (Conditional ol _ _ _) l f r _ ->
          fsep [if isCond ol then parens l else l,
                text whenS <+> f, text elseS <+> r]
    , foldMixfix_qual_pred = \ _ p -> printPredSymb p
    , foldMixfix_term = \ (Mixfix_term ol) l -> case ol of
          [_, Mixfix_parenthesized _ _] -> fcat l
          _ -> fsep l
    , foldMixfix_token = \ _ -> sidDoc
    , foldMixfix_sorted_term = \ _ s _ -> colon <+> idDoc s
    , foldMixfix_cast = \ _ s _ -> text asS <+> idDoc s
    , foldMixfix_parenthesized = \ _ l _ -> parens $ sepByCommas l
    , foldMixfix_bracketed = \ _ l _ -> brackets $ sepByCommas l
    , foldMixfix_braced = \ _ l _ -> specBraces $ sepByCommas l }

recoverType :: [Constraint] -> [Annoted DATATYPE_DECL]
recoverType =
  map (\ c -> let s = newSort c in emptyAnno $ Datatype_decl s
      (map (\ (o, _) -> case o of
      Qual_op_name i (Op_type fk args _ ps) r ->
          let qs = appRange ps r in emptyAnno $ case args of
            [_] | isInjName i -> Subsorts args qs
            _ -> Alt_construct fk i (map Sort args) qs
      _ -> error "CASL.recoverType") $ opSymbs c) nullRange)

zipConds :: [TERM f] -> [Doc] -> [Doc]
zipConds = zipWith (\ o d -> if isCond o then parens d else d)

printFormula :: (f -> Doc) -> FORMULA f -> Doc
printFormula mf = foldFormula $ printRecord mf

instance Pretty f => Pretty (FORMULA f) where
    pretty = printFormula pretty

printTerm :: (f -> Doc) -> TERM f -> Doc
printTerm mf = foldTerm $ printRecord mf

instance Pretty f => Pretty (TERM f) where
    pretty = printTerm pretty

isQuant :: FORMULA f -> Bool
isQuant f = case f of
    Quantification _ _ _ _ -> True
    ExtFORMULA _ -> True
    Conjunction l _ -> case l of
        [] -> False
        _ -> isQuant $ last l
    Disjunction l _ ->  case l of
        [] -> False
        _ -> isQuant $ last l
    Implication a b impl _ -> isQuant $ if impl then b else a
    Equivalence _ b _ -> isQuant b
    Negation a _ -> isQuant a
    _ -> False

isEquiv :: FORMULA f -> Bool
isEquiv f = case f of
    Equivalence _ _ _ -> True
    _ -> False

isAnyImpl :: FORMULA f -> Bool
isAnyImpl f = isImpl True f || isImpl False f

isJunct :: FORMULA f -> Bool
isJunct f = case f of
    Conjunction _ _ -> True
    Disjunction _ _ -> True
    _ -> isAnyImpl f

-- true for non-final
mkJunctDoc :: Bool -> FORMULA f -> Doc -> Doc
mkJunctDoc b f = if isJunct f || b && isQuant f then parens else id

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

-- |
-- a helper class for calculating the pluralS of e.g. ops
class ListCheck a where
    innerList :: a -> [()]

instance ListCheck Token where
    innerList _ = [()]

instance ListCheck Id where
    innerList _ = [()]

instance ListCheck a => ListCheck [a] where
    innerList = concatMap innerList

-- |
-- an instance of ListCheck for Annoted stuff
instance ListCheck a => ListCheck (Annoted a) where
    innerList = innerList . item

-- |
-- pluralS checks a list with elements in class ListCheck for a list
-- greater than zero. It returns an empty String if the list and all
-- nested lists have only one element. If the list or an nested list
-- has more than one element a String containig one "s" is returned.
pluralS :: ListCheck a => a -> String
pluralS l = if isSingle $ innerList l then "" else "s"

-- instances of ListCheck for various data types of AS_Basic_CASL

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

-- | print a formula as a sentence
printTheoryFormula :: Pretty f => Named (FORMULA f) -> Doc
printTheoryFormula f = printAnnoted
    ((case sentence f of
    Quantification Universal _ _ _ -> id
    Sort_gen_ax _ _ -> id
    _ -> (bullet <+>)) . pretty) $ fromLabelledSen f
