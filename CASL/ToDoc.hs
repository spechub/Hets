{- |
Module      :  ./CASL/ToDoc.hs
Description :  pretty printing data types of BASIC_SPEC
Copyright   :  (c) Christian Maeder and Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

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
    , pluralS_symb_list
    , pluralS
    , appendS
    , isJunct
    , printInfix
    , ListCheck (..)
    , recoverType
    , printALTERNATIVE
    , typeString
    , printVarDecl
    , printVarDeclL
    , printVarDecls
    , printOptArgDecls
    , printSortItem
    , printOpItem
    , printPredItem
    , printPredHead
    , printRecord
    , printAttr
    , printAnnotedBulletFormulas
    , FormExtension (..)
    , isQuant
    ) where

import Common.Id
import Common.Keywords
import Common.Doc
import Common.DocUtils
import Common.AS_Annotation

import CASL.AS_Basic_CASL
import CASL.Fold

instance (Pretty b, Pretty s, FormExtension f) => Pretty (BASIC_SPEC b s f)
  where pretty = printBASIC_SPEC pretty pretty

printBASIC_SPEC :: FormExtension f => (b -> Doc) -> (s -> Doc)
                -> BASIC_SPEC b s f -> Doc
printBASIC_SPEC fB fS (Basic_spec l) = case l of
    [] -> specBraces empty
    _ -> vcat $ map (printAnnoted (printBASIC_ITEMS fB fS)) l

instance (Pretty b, Pretty s, FormExtension f) => Pretty (BASIC_ITEMS b s f)
  where pretty = printBASIC_ITEMS pretty pretty

typeString :: SortsKind -> [Annoted DATATYPE_DECL] -> String
typeString sk l = (case sk of
    NonEmptySorts -> typeS
    PossiblyEmptySorts -> etypeS) ++ appendS l

printBASIC_ITEMS :: FormExtension f => (b -> Doc) -> (s -> Doc)
                 -> BASIC_ITEMS b s f -> Doc
printBASIC_ITEMS fB fS sis = case sis of
    Sig_items s -> printSIG_ITEMS fS s
    Free_datatype sk l _ -> sep [keyword freeS <+> keyword (typeString sk l),
                                 semiAnnos printDATATYPE_DECL l]
    Sort_gen l _ -> case l of
         [Annoted (Datatype_items sk l' _) _ las ras] ->
             (if null las then id else (printAnnotationList las $+$))
             $ (if null ras then id else ($+$ printAnnotationList ras))
             $ sep [keyword generatedS <+> keyword (typeString sk l'),
                    semiAnnos printDATATYPE_DECL l']
         _ -> sep [keyword generatedS, specBraces $ vcat $ map
              (printAnnoted $ printSIG_ITEMS fS) l]
    Var_items l _ -> topSigKey (varS ++ pluralS l) <+> printVarDecls l
    Local_var_axioms l f _ ->
            fsep [fsep $ forallDoc : printVarDeclL l
                 , printAnnotedBulletFormulas f]
    Axiom_items f _ -> printAnnotedBulletFormulas f
    Ext_BASIC_ITEMS b -> fB b

printAnnotedBulletFormulas :: FormExtension f => [Annoted (FORMULA f)] -> Doc
printAnnotedBulletFormulas l = vcat $ case l of
    [] -> []
    _ -> let pp = addBullet . printFormula in
         map (printAnnoted pp) (init l)
         ++ [printSemiAnno pp False $ last l] -- use True for HasCASL

instance (Pretty s, FormExtension f) => Pretty (SIG_ITEMS s f) where
    pretty = printSIG_ITEMS pretty

printSIG_ITEMS :: FormExtension f => (s -> Doc) -> SIG_ITEMS s f -> Doc
printSIG_ITEMS fS sis = case sis of
    Sort_items sk l _ -> topSigKey ((case sk of
        NonEmptySorts -> sortS
        PossiblyEmptySorts -> esortS) ++ pluralS l) <+>
         semiAnnos printSortItem l
    Op_items l _ -> topSigKey (opS ++ pluralS l) <+>
        let pp = printOpItem in
        if null l then empty else if case item $ last l of
            Op_decl _ _ a@(_ : _) _ -> case last a of
                Unit_op_attr {} -> False  -- use True for HasCASL
                _ -> False
            Op_defn {} -> False  -- use True for HasCASL
            _ -> False
        then vcat $ map (printSemiAnno pp True) l else semiAnnos pp l
    Pred_items l _ -> topSigKey (predS ++ pluralS l) <+>
        let pp = printPredItem in
        if null l then empty else if case item $ last l of
            Pred_defn {} -> True
            _ -> False
        then vcat $ map (printSemiAnno pp True) l else semiAnnos pp l
    Datatype_items sk l _ -> topSigKey (typeString sk l) <+>
             semiAnnos printDATATYPE_DECL l
    Ext_SIG_ITEMS s -> fS s

printDATATYPE_DECL :: DATATYPE_DECL -> Doc
printDATATYPE_DECL (Datatype_decl s a r) =
    let pa = printAnnoted printALTERNATIVE in case a of
    [] -> printDATATYPE_DECL (Datatype_decl s [emptyAnno $ Subsorts [s] r] r)
    h : t -> sep [idLabelDoc s, colon <> colon <> sep
                      ((equals <+> pa h) :
                       map ((bar <+>) . pa) t)]

instance Pretty DATATYPE_DECL where
    pretty = printDATATYPE_DECL

printCOMPONENTS :: COMPONENTS -> Doc
printCOMPONENTS c = case c of
    Cons_select k l s _ -> fsep $ punctuate comma (map idLabelDoc l)
           ++ [case k of
           Total -> colon
           Partial -> colon <> quMarkD, idDoc s]
    Sort s -> idDoc s

instance Pretty COMPONENTS where
    pretty = printCOMPONENTS

printALTERNATIVE :: ALTERNATIVE -> Doc
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

printSortItem :: FormExtension f => SORT_ITEM f -> Doc
printSortItem si = case si of
    Sort_decl sl _ -> sepByCommas $ map idLabelDoc sl
    Subsort_decl sl sup _ ->
        fsep $ punctuate comma (map idDoc sl) ++ [less, idDoc sup]
    Subsort_defn s v sup af _ -> fsep [idLabelDoc s, equals,
              specBraces $ fsep [sidDoc v, colon <+> idDoc sup,
                             printAnnoted (addBullet . printFormula) af]]
    Iso_decl sl _ -> fsep $ punctuate (space <> equals) $ map idDoc sl

instance FormExtension f => Pretty (SORT_ITEM f) where
    pretty = printSortItem

printQuant :: QUANTIFIER -> Doc
printQuant q = case q of
    Universal -> forallDoc
    Existential -> exists
    Unique_existential -> unique

printSortedVars :: [VAR] -> SORT -> Doc
printSortedVars l s =
    fsep $ punctuate comma (map sidDoc l) ++ [colon <+> idDoc s]

printVarDeclL :: [VAR_DECL] -> [Doc]
printVarDeclL = punctuate semi . map printVarDecl

printVarDecls :: [VAR_DECL] -> Doc
printVarDecls = fsep . printVarDeclL

printVarDecl :: VAR_DECL -> Doc
printVarDecl (Var_decl l s _) = printSortedVars l s

printArgDecls :: [VAR_DECL] -> Doc
printArgDecls = parens . printVarDecls

printOptArgDecls :: [VAR_DECL] -> Doc
printOptArgDecls vs = if null vs then empty else printArgDecls vs

printPredHead :: PRED_HEAD -> Doc
printPredHead (Pred_head l _) = printArgDecls l

printPredItem :: FormExtension f => PRED_ITEM f -> Doc
printPredItem p = case p of
    Pred_decl l t _ -> fsep $ punctuate comma (map idLabelDoc l)
        ++ [colon <+> printPredType t]
    Pred_defn i h f _ ->
        sep [ cat [idLabelDoc i, printPredHead h]
           , equiv <+> printAnnoted printFormula f]

instance FormExtension f => Pretty (PRED_ITEM f) where
    pretty = printPredItem

printAttr :: FormExtension f => OP_ATTR f -> Doc
printAttr a = case a of
    Assoc_op_attr -> text assocS
    Comm_op_attr -> text commS
    Idem_op_attr -> text idemS
    Unit_op_attr t -> text unitS <+> printTerm t

instance FormExtension f => Pretty (OP_ATTR f) where
    pretty = printAttr

printOpHead :: OP_HEAD -> Doc
printOpHead (Op_head k l mr _) =
    sep $ printOptArgDecls l : case mr of
      Nothing -> []
      Just r -> [(case k of
             Total -> colon
             Partial -> text colonQuMark) <+> idDoc r]

instance Pretty OP_HEAD where
    pretty = printOpHead

printOpItem :: FormExtension f => OP_ITEM f -> Doc
printOpItem p = case p of
    Op_decl l t a _ -> fsep $ punctuate comma (map idLabelDoc l)
        ++ [colon <> (if null a then id else (<> comma)) (printOpType t)]
        ++ punctuate comma (map printAttr a)
    Op_defn i h@(Op_head _ l _ _) t _ ->
        sep [ (if null l then sep else cat) [idLabelDoc i, printOpHead h]
            , equals <+> printAnnoted printTerm t]

instance FormExtension f => Pretty (OP_ITEM f) where
    pretty = printOpItem

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
    A_type s -> space <> idDoc s

print_kind_text :: SYMB_KIND -> [a] -> Doc
print_kind_text k l = case k of
    Implicit -> empty
    _ -> keyword (pluralS_symb_list k l)

pluralS_symb_list :: SYMB_KIND -> [a] -> String
pluralS_symb_list k l = (case k of
    Implicit -> error "pluralS_symb_list"
    Sorts_kind -> sortS
    Ops_kind -> opS
    Preds_kind -> predS) ++ appendS l

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

-- possibly use "printInfix False vcat"
printInfix :: Bool -- ^ attach separator to right argument?
           -> ([Doc] -> Doc) -- ^ combinator for two docs
           -> Doc -> Doc -> Doc -- ^ left, separator and right arguments
           -> Doc
printInfix b join l s r =
     join $ if b then [l, s <+> r] else [l <+> s, r]

class (GetRange f, Pretty f) => FormExtension f where
  isQuantifierLike :: f -> Bool
  isQuantifierLike _ = False
  prefixExt :: f -> Doc -> Doc
  prefixExt _ = (bullet <+>)

instance FormExtension ()

printRecord :: FormExtension f => Record f Doc Doc
printRecord = Record
    { foldQuantification = \ _ q l r _ ->
          fsep $ printQuant q : printVarDeclL l
                                ++ [addBullet r]
    , foldJunction = \ o j l _ ->
        let (n, p) = case j of
                  Con -> (trueS, andDoc)
                  Dis -> (falseS, orDoc)
        in case o of
          Junction _ ol@(_ : _) _ -> fsep $ prepPunctuate (p <> space)
               $ zipWith (mkJunctDoc True) (init ol) (init l) ++
                 [mkJunctDoc False (last ol) (last l)]
          _ -> text n
    , foldRelation = \ o l c r _ ->
          let Relation oL _ oR _ = o
              b = c == Implication
              nl = if isAnyImpl oL || b && isQuant oL
                   then parens l else l
              nr = if isImpl c oR || not b && isQuant oR
                   then parens r else r
          in case c of
               Implication -> printInfix True sep nl implies nr
               RevImpl -> printInfix True sep nr (text ifS) nl
               Equivalence -> printInfix True sep
                 (if isQuant oL then parens l else mkEquivDoc oL l)
                 equiv $ mkEquivDoc oR r
    , foldNegation = \ orig r _ -> case orig of
          Negation o _ -> hsep [notDoc, mkJunctDoc False o r]
          _ -> error "CASL.ToDoc.printRecord.foldNegation"
    , foldAtom = \ _ b _ -> text $ if b then trueS else falseS
    , foldPredication = \ o p l _ -> case (p, o) of
          (Pred_name i, Predication _ ol _) -> predIdApplDoc i $ zipConds ol l
          _ -> if null l then printPredSymb p else
              fcat [printPredSymb p, parens $ sepByCommas l]
    , foldDefinedness = \ _ r _ -> hsep [text defS, r]
    , foldEquation = \ _ l e r _ -> printInfix True sep l (case e of
        Existl -> exequal
        Strong -> equals) r
    , foldMembership = \ _ r t _ -> fsep [r, inDoc, idDoc t]
    , foldMixfix_formula = \ _ r -> r
    , foldSort_gen_ax = \ o _ _ ->
        let Sort_gen_ax constrs b = o
            l = recoverType constrs
            genAx = sep [ keyword generatedS <+> keyword (typeS ++ appendS l)
                        , semiAnnos printDATATYPE_DECL l]
        in if b then text "%% free" $+$ genAx else genAx
    , foldQuantOp = \ _ o n r -> fsep
        [ forallDoc
        , parens . printOpSymb $ mkQualOp o n
        , addBullet r ]
    , foldQuantPred = \ _ p n r -> fsep
        [ forallDoc
        , printPredSymb $ mkQualPred p n
        , addBullet r ]
    , foldExtFORMULA = const pretty
    , foldQual_var = \ _ v s _ ->
          parens $ fsep [text varS, sidDoc v, colon <+> idDoc s]
    , foldApplication = \ orig o l _ -> case (o, orig) of
          (Op_name i, Application _ ol _) -> idApplDoc i $ zipConds ol l
          _ -> let d = parens $ printOpSymb o in
              if null l then d else fcat [d, parens $ sepByCommas l]
    , foldSorted_term = \ _ r t _ -> fsep [idApplDoc typeId [r], idDoc t]
    , foldCast = \ _ r t _ ->
          fsep [idApplDoc (mkId [placeTok, mkSimpleId asS]) [r], idDoc t]
    , foldConditional = \ o l f r _ -> case o of
          Conditional ol _ _ _ -> fsep [if isCond ol then parens l else l,
                text whenS <+> f, text elseS <+> r]
          _ -> error "CASL.ToDoc.printRecord.foldConditional"
    , foldMixfix_qual_pred = const printPredSymb
    , foldMixfix_term = \ o l -> case o of
          Mixfix_term [_, Mixfix_parenthesized _ _] -> fcat l
          _ -> fsep l
    , foldMixfix_token = const sidDoc
    , foldMixfix_sorted_term = \ _ s _ -> colon <+> idDoc s
    , foldMixfix_cast = \ _ s _ -> text asS <+> idDoc s
    , foldMixfix_parenthesized = \ _ l _ -> parens $ sepByCommas l
    , foldMixfix_bracketed = \ _ l _ -> brackets $ sepByCommas l
    , foldMixfix_braced = \ _ l _ -> specBraces $ sepByCommas l
    , foldExtTERM = const pretty }

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

printFormula :: FormExtension f => FORMULA f -> Doc
printFormula = foldFormula printRecord

instance FormExtension f => Pretty (FORMULA f) where
    pretty = printFormula

printTerm :: FormExtension f => TERM f -> Doc
printTerm = foldTerm printRecord

instance FormExtension f => Pretty (TERM f) where
    pretty = printTerm

isQuant :: FormExtension f => FORMULA f -> Bool
isQuant f = case f of
    Quantification {} -> True
    ExtFORMULA ef -> isQuantifierLike ef
    Junction _ l _ -> case l of
        [] -> False
        _ -> isQuant $ last l
    Relation a c b _ -> isQuant $ if c == RevImpl then a else b
    Negation a _ -> isQuant a
    _ -> False

isEquiv :: FORMULA f -> Bool
isEquiv f = case f of
    Relation _ c _ _ -> c == Equivalence
    _ -> False

isAnyImpl :: FORMULA f -> Bool
isAnyImpl f = isImpl Implication f || isImpl RevImpl f

isJunct :: FORMULA f -> Bool
isJunct f = case f of
    Junction {} -> True
    _ -> isAnyImpl f

-- true for non-final
mkJunctDoc :: FormExtension f => Bool -> FORMULA f -> Doc -> Doc
mkJunctDoc b f = if isJunct f || b && isQuant f then parens else id

mkEquivDoc :: FORMULA f -> Doc -> Doc
mkEquivDoc f = if isEquiv f then parens else id

isImpl :: Relation -> FORMULA f -> Bool
isImpl a f = case f of
    Relation _ c _ _ -> c == Equivalence || a /= c
    _ -> False

isCond :: TERM f -> Bool
isCond t = case t of
    Conditional {} -> True
    _ -> False

-- | a helper class for calculating the pluralS of e.g. ops
class ListCheck a where
    innerList :: a -> [()]

instance ListCheck Token where
    innerList _ = [()]

instance ListCheck Id where
    innerList _ = [()]

instance ListCheck a => ListCheck [a] where
    innerList = concatMap innerList

-- | an instance of ListCheck for Annoted stuff
instance ListCheck a => ListCheck (Annoted a) where
    innerList = innerList . item

{- | pluralS checks nested lists via the class ListCheck to decide
if a plural s should be appended. -}
pluralS :: ListCheck a => a -> String
pluralS = appendS . innerList

appendS :: [a] -> String
appendS l = if isSingle l then "" else "s"

-- instances of ListCheck for various data types of AS_Basic_CASL

instance ListCheck (SORT_ITEM f) where
    innerList (Sort_decl l _) = innerList l
    innerList (Subsort_decl l _ _) = innerList l
    innerList (Subsort_defn {}) = [()]
    innerList (Iso_decl l _) = innerList $ drop 1 l
      -- assume last sort is known

instance ListCheck (OP_ITEM f) where
    innerList (Op_decl l _ _ _) = innerList l
    innerList (Op_defn {}) = [()]

instance ListCheck (PRED_ITEM f) where
    innerList (Pred_decl l _ _) = innerList l
    innerList (Pred_defn {}) = [()]

instance ListCheck VAR_DECL where
    innerList (Var_decl l _ _) = innerList l

-- | print a formula as a sentence
printTheoryFormula :: FormExtension f => Named (FORMULA f) -> Doc
printTheoryFormula f = printAnnoted
    ((case sentence f of
    Quantification Universal _ _ _ -> id
    Sort_gen_ax _ _ -> id
    ExtFORMULA e -> prefixExt e
    _ -> (bullet <+>)) . pretty) $ fromLabelledSen f
