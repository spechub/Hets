{- |
Module      :  ./THF/PrintTHF.hs
Description :  A printer for the TPTP-THF Syntax
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

A printer for the TPTP-THF Input Syntax v5.1.0.2 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module THF.PrintTHF where

import THF.As

import Data.Char

import Common.Doc
import Common.DocUtils
import Common.Id (Token)

{- -----------------------------------------------------------------------------
Pretty Instances for the THF and THF0 Syntax.
Most methods match those of As.hs
----------------------------------------------------------------------------- -}

printTPTPTHF :: [TPTP_THF] -> Doc
printTPTPTHF [] = empty
printTPTPTHF (t : rt) = case t of
    TPTP_THF_Annotated_Formula {} -> pretty t $++$ printTPTPTHF rt
    _ -> pretty t $+$ printTPTPTHF rt

instance Pretty TPTP_THF where
    pretty t = case t of
        TPTP_THF_Annotated_Formula n fr f a ->
            text "thf" <> parens (pretty n <> comma
                <+> pretty fr <> comma
                <+> pretty f <> pretty a)
            <> text "."
        TPTP_Include i -> pretty i
        TPTP_Comment c -> pretty c
        TPTP_Defined_Comment dc -> pretty dc
        TPTP_System_Comment sc -> pretty sc
        TPTP_Header h -> prettyHeader h

prettyHeader :: [Comment] -> Doc
prettyHeader = foldr (($+$) . pretty) empty

instance Pretty Comment where
    pretty c = case c of
        Comment_Line s -> text "%" <> (text . show) s
        Comment_Block sl -> text "/*"
                $+$ prettyCommentBlock (lines $ show sl)
                $+$ text "*/"

instance Pretty DefinedComment where
    pretty dc = case dc of
        Defined_Comment_Line s -> text "%$" <> (text . show) s
        Defined_Comment_Block sl -> text "/*$"
                $+$ prettyCommentBlock (lines $ show sl)
                $+$ text "*/"

instance Pretty SystemComment where
    pretty sc = case sc of
        System_Comment_Line s -> text "%$$" <> (text . show) s
        System_Comment_Block sl -> text "/*$$"
                $+$ prettyCommentBlock (lines $ show sl)
                $+$ text "*/"

prettyCommentBlock :: [String] -> Doc
prettyCommentBlock = foldr (($+$) . text) empty

instance Pretty Include where
    pretty (I_Include fn nl) = text "include" <> parens (prettySingleQuoted fn
        <> maybe empty (\ c -> comma <+> prettyNameList c) nl) <> text "."

instance Pretty Annotations where
    pretty a = case a of
        Annotations s o -> comma <+> pretty s <> prettyOptionalInfo o
        Null -> empty

instance Pretty FormulaRole where
    pretty fr = text $ map toLower (show fr)

instance Pretty THFFormula where
    pretty f = case f of
        TF_THF_Logic_Formula lf -> pretty lf
        TF_THF_Sequent s -> pretty s
        T0F_THF_Typed_Const tc -> pretty tc

instance Pretty THFLogicFormula where
    pretty lf = case lf of
        TLF_THF_Binary_Formula bf -> pretty bf
        TLF_THF_Unitary_Formula uf -> pretty uf
        TLF_THF_Type_Formula tf -> pretty tf
        TLF_THF_Sub_Type st -> pretty st

instance Pretty THFBinaryFormula where
    pretty bf = case bf of
        TBF_THF_Binary_Tuple bt -> pretty bt
        TBF_THF_Binary_Type bt -> pretty bt
        TBF_THF_Binary_Pair uf1 pc uf2 ->
            pretty uf1 <+> pretty pc <+> pretty uf2

instance Pretty THFBinaryTuple where
    pretty bt = case bt of
        TBT_THF_Or_Formula ufl -> sepBy (map pretty ufl) orSign
        TBT_THF_And_Formula ufl -> sepBy (map pretty ufl) andSign
        TBT_THF_Apply_Formula ufl -> sepBy (map pretty ufl) applySign

instance Pretty THFUnitaryFormula where
    pretty tuf = case tuf of
        TUF_THF_Quantified_Formula qf -> pretty qf
        TUF_THF_Unary_Formula uc lf -> pretty uc <+> parens (pretty lf)
        TUF_THF_Atom a -> pretty a
        TUF_THF_Tuple t -> prettyTuple t
        TUF_THF_Conditional lf1 lf2 lf3 ->
            text "$itef" <> parens (pretty lf1
            <> comma <+> pretty lf2
            <> comma <+> pretty lf3)
        TUF_THF_Logic_Formula_Par l -> parens (pretty l)
        T0UF_THF_Abstraction vl uf -> text "^" <+>
            brackets (prettyVariableList vl) <+> text ":" <+> pretty uf

instance Pretty THFQuantifiedFormula where
    pretty qf = case qf of
        TQF_THF_Quantified_Formula tq vl uf -> pretty tq <+>
            brackets (prettyVariableList vl) <+> text ":" <+> pretty uf
        T0QF_THF_Quantified_Var q vl uf -> pretty q <+>
            brackets (prettyVariableList vl) <+> text ":" <+> pretty uf
        T0QF_THF_Quantified_Novar tq uf ->
            pretty tq <+> parens (pretty uf)

prettyVariableList :: THFVariableList -> Doc
prettyVariableList vl = sepByCommas (map pretty vl)

instance Pretty THFVariable where
    pretty v = case v of
        TV_THF_Typed_Variable va tlt -> prettyUpperWord va
            <+> text ":" <+> pretty tlt
        TV_Variable var -> prettyUpperWord var

instance Pretty THFTypedConst where
    pretty ttc = case ttc of
        T0TC_Typed_Const c tlt -> prettyConstant c <+> text ":"
            <+> pretty tlt
        T0TC_THF_TypedConst_Par tc -> parens (pretty tc)

instance Pretty THFTypeFormula where
    pretty ttf = case ttf of
        TTF_THF_Type_Formula tf tlt -> pretty tf <+> text ":" <+> pretty tlt
        TTF_THF_Typed_Const c tlt -> prettyConstant c <+> text ":"
            <+> pretty tlt

instance Pretty THFTypeableFormula where
    pretty tbf = case tbf of
        TTyF_THF_Atom a -> pretty a
        TTyF_THF_Tuple t -> prettyTuple t
        TTyF_THF_Logic_Formula lf -> parens $ pretty lf

instance Pretty THFSubType where
    pretty (TST_THF_Sub_Type c1 c2) =
        prettyConstant c1 <+> text "<<" <+> prettyConstant c2

instance Pretty THFTopLevelType where
    pretty tlt = case tlt of
        TTLT_THF_Logic_Formula lf -> pretty lf
        T0TLT_Constant c -> prettyConstant c
        T0TLT_Variable v -> prettyUpperWord v
        T0TLT_Defined_Type dt -> pretty dt
        T0TLT_System_Type st -> prettyAtomicSystemWord st
        T0TLT_THF_Binary_Type bt -> pretty bt

instance Pretty THFUnitaryType where
    pretty ut = case ut of
        TUT_THF_Unitary_Formula uf -> pretty uf
        T0UT_Constant c -> prettyConstant c
        T0UT_Variable v -> prettyUpperWord v
        T0UT_Defined_Type dt -> pretty dt
        T0UT_System_Type st -> prettyAtomicSystemWord st
        T0UT_THF_Binary_Type_Par bt -> parens (pretty bt)

instance Pretty THFBinaryType where
    pretty tbt = case tbt of
        TBT_THF_Mapping_Type utl -> sepBy (map pretty utl) arrowSign
        TBT_THF_Xprod_Type utl -> sepBy (map pretty utl) starSign
        TBT_THF_Union_Type utl -> sepBy (map pretty utl) plusSign
        T0BT_THF_Binary_Type_Par bt -> parens (pretty bt)

instance Pretty THFAtom where
    pretty a = case a of
        TA_Term t -> pretty t
        TA_THF_Conn_Term ct -> pretty ct
        TA_Defined_Type dt -> pretty dt
        TA_Defined_Plain_Formula dp -> pretty dp
        TA_System_Type st -> prettyAtomicSystemWord st
        TA_System_Atomic_Formula st -> pretty st
        T0A_Constant c -> prettyConstant c
        T0A_Defined_Constant dc -> prettyAtomicDefinedWord dc
        T0A_System_Constant sc -> prettyAtomicSystemWord sc
        T0A_Variable v -> prettyUpperWord v

prettyTuple :: THFTuple -> Doc
prettyTuple ufl = brackets $ sepByCommas (map pretty ufl)

instance Pretty THFSequent where
    pretty (TS_THF_Sequent_Par s) = parens $ pretty s
    pretty (TS_THF_Sequent t1 t2) =
        prettyTuple t1 <+> text "-->" <+> prettyTuple t2

instance Pretty THFConnTerm where
    pretty ct = case ct of
        TCT_THF_Pair_Connective pc -> pretty pc
        TCT_Assoc_Connective ac -> pretty ac
        TCT_THF_Unary_Connective uc -> pretty uc
        T0CT_THF_Quantifier q -> pretty q

instance Pretty THFQuantifier where
    pretty q = case q of
        TQ_ForAll -> text "!"
        TQ_Exists -> text "?"
        TQ_Lambda_Binder -> text "^"
        TQ_Dependent_Product -> text "!>"
        TQ_Dependent_Sum -> text "?*"
        TQ_Indefinite_Description -> text "@+"
        TQ_Definite_Description -> text "@-"
        T0Q_PiForAll -> text "!!"
        T0Q_SigmaExists -> text "??"

instance Pretty Quantifier where
    pretty q = case q of
        T0Q_ForAll -> text "!"
        T0Q_Exists -> text "?"

instance Pretty THFPairConnective where
    pretty pc = case pc of
        Infix_Equality -> text "="
        Infix_Inequality -> text "!="
        Equivalent -> text "<=>"
        Implication -> text "=>"
        IF -> text "<="
        XOR -> text "<~>"
        NOR -> text "~|"
        NAND -> text "~&"

instance Pretty THFUnaryConnective where
    pretty uc = case uc of
        Negation -> text "~"
        PiForAll -> text "!!"
        SigmaExists -> text "??"

instance Pretty AssocConnective where
    pretty AND = text "&"
    pretty OR = text "|"

instance Pretty DefinedType where
    pretty DT_oType = text "$o"
    pretty dt = text $ '$' : drop 3 (show dt)

instance Pretty DefinedPlainFormula where
    pretty dpf = case dpf of
        DPF_Defined_Prop dp -> pretty dp
        DPF_Defined_Formula dp a -> pretty dp <> parens (prettyArguments a)

instance Pretty DefinedProp where
    pretty DP_True = text "$true"
    pretty DP_False = text "$false"

instance Pretty DefinedPred where
    pretty dp = text $ '$' : map toLower (show dp)

instance Pretty Term where
    pretty t = case t of
        T_Function_Term ft -> pretty ft
        T_Variable v -> prettyUpperWord v

instance Pretty FunctionTerm where
    pretty ft = case ft of
        FT_Plain_Term pt -> pretty pt
        FT_Defined_Term dt -> pretty dt
        FT_System_Term st -> pretty st

instance Pretty PlainTerm where
    pretty pt = case pt of
        PT_Constant c -> prettyConstant c
        PT_Plain_Term f a -> pretty f <> parens (prettyArguments a)

prettyConstant :: Constant -> Doc
prettyConstant = pretty

instance Pretty DefinedTerm where
    pretty dt = case dt of
        DT_Defined_Atom da -> pretty da
        DT_Defined_Atomic_Term dpt -> pretty dpt

instance Pretty DefinedAtom where
    pretty da = case da of
        DA_Number n -> pretty n
        DA_Distinct_Object dio -> prettyDistinctObject dio

instance Pretty DefinedPlainTerm where
    pretty dpt = case dpt of
        DPT_Defined_Constant df -> pretty df
        DPT_Defined_Function df a -> pretty df <> parens (prettyArguments a)

instance Pretty DefinedFunctor where
    pretty df = text $ '$' : map toLower (show df)

instance Pretty SystemTerm where
    pretty st = case st of
        ST_System_Constant sf -> prettyAtomicSystemWord sf
        ST_System_Term sf a -> prettyAtomicSystemWord sf
            <> parens (prettyArguments a)

prettyArguments :: Arguments -> Doc
prettyArguments = sepByCommas . map pretty

instance Pretty PrincipalSymbol where
    pretty ps = case ps of
        PS_Functor f -> pretty f
        PS_Variable v -> prettyUpperWord v

instance Pretty Source where
    pretty s = case s of
        S_Dag_Source ds -> pretty ds
        S_Internal_Source it oi -> text "introduced" <> parens (
            pretty it <> prettyOptionalInfo oi)
        S_External_Source es -> pretty es
        S_Sources ss -> sepByCommas (map pretty ss)
        S_Unknown -> text "unknown"

instance Pretty DagSource where
    pretty ds = case ds of
        DS_Name n -> pretty n
        DS_Inference_Record aw ui pl -> text "inference"
            <> parens (pretty aw <> comma <+> prettyUsefulInfo ui
            <> comma <+> brackets (sepByCommas (map pretty pl)))

instance Pretty ParentInfo where
    pretty (PI_Parent_Info s mgl) =
        let gl = maybe empty (\ c -> text ":" <> prettyGeneralList c) mgl
        in pretty s <> gl

instance Pretty IntroType where
    pretty it = text (drop 3 (show it))

instance Pretty ExternalSource where
    pretty es = case es of
        ES_File_Source fs -> pretty fs
        ES_Theory tn oi -> text "theory" <> parens (
            pretty tn <> prettyOptionalInfo oi)
        ES_Creator_Source aw oi -> text "creator" <> parens (
            pretty aw <> prettyOptionalInfo oi)

instance Pretty FileSource where
    pretty (FS_File fn mn) =
        let n = maybe empty (\ c -> comma <+> pretty c) mn
        in text "file" <> parens (prettySingleQuoted fn <> n)

instance Pretty TheoryName where
    pretty tn = text $ map toLower (show tn)

prettyOptionalInfo :: OptionalInfo -> Doc
prettyOptionalInfo = maybe empty (\ ui -> comma <+> prettyUsefulInfo ui)

prettyUsefulInfo :: UsefulInfo -> Doc
prettyUsefulInfo = brackets . sepByCommas . map pretty

instance Pretty InfoItem where
    pretty ii = case ii of
        II_Formula_Item fi -> pretty fi
        II_Inference_Item infi -> pretty infi
        II_General_Function gf -> pretty gf

instance Pretty FormulaItem where
    pretty fi = case fi of
        FI_Description_Item aw -> text "description" <> parens (pretty aw)
        FI_Iquote_Item aw -> text "iquote" <> parens (pretty aw)

instance Pretty InferenceItem where
    pretty ii = case ii of
        II_Inference_Status is -> pretty is
        II_Assumptions_Record nl -> text "assumptions"
            <> parens (brackets (prettyNameList nl))
        II_New_Symbol_Record aw psl -> text "new_symbols" <> parens (pretty aw
            <> comma <+> brackets (sepByCommas (map pretty psl)))
        II_Refutation fs -> text "refutation" <> parens (pretty fs)

instance Pretty InferenceStatus where
    pretty is = case is of
        IS_Status s -> text "status" <> parens (pretty s)
        IS_Inference_Info aw1 aw2 gl -> pretty aw1 <> parens (pretty aw2
            <> comma <+> prettyGeneralList gl)

instance Pretty StatusValue where
    pretty sv = text $ map toLower (show sv)

prettyNameList :: NameList -> Doc
prettyNameList = sepByCommas . map pretty

instance Pretty GeneralTerm where
    pretty gt = case gt of
        GT_General_Data gd -> pretty gd
        GT_General_Data_Term gd gt1 -> pretty gd <+> text ":" <+> pretty gt1
        GT_General_List gl -> prettyGeneralList gl

instance Pretty GeneralData where
    pretty gd = case gd of
        GD_Atomic_Word aw -> pretty aw
        GD_General_Function gf -> pretty gf
        GD_Variable v -> prettyUpperWord v
        GD_Number n -> pretty n
        GD_Distinct_Object dio -> prettyDistinctObject dio
        GD_Formula_Data fd -> pretty fd
        GD_Bind v fd -> text "bind" <> parens (
            prettyUpperWord v <> comma <+> pretty fd)

instance Pretty GeneralFunction where
    pretty (GF_General_Function aw gts) =
        pretty aw <> parens (prettyGeneralTerms gts)

instance Pretty FormulaData where
    pretty (THF_Formula thff) = text "$thf" <> parens (pretty thff)

prettyGeneralList :: GeneralList -> Doc
prettyGeneralList = brackets . prettyGeneralTerms

prettyGeneralTerms :: GeneralTerms -> Doc
prettyGeneralTerms = sepByCommas . map pretty

instance Pretty Name where
    pretty n = case n of
        N_Atomic_Word a -> pretty a
        N_Integer s -> text $ show s
        T0N_Unsigned_Integer s -> text $ show s

instance Pretty AtomicWord where
    pretty a = case a of
        A_Single_Quoted s -> prettySingleQuoted s
        A_Lower_Word l -> prettyLowerWord l

prettyAtomicSystemWord :: Token -> Doc
prettyAtomicSystemWord asw = text ("$$" ++ show asw)

prettyAtomicDefinedWord :: Token -> Doc
prettyAtomicDefinedWord adw = text ('$' : show adw)

instance Pretty Number where
    pretty n = case n of
        Num_Integer i -> text $ show i
        Num_Rational ra -> text $ show ra
        Num_Real re -> text $ show re

prettySingleQuoted :: Token -> Doc
prettySingleQuoted s = text "\'" <> (text . show) s <> text "\'"

prettyDistinctObject :: Token -> Doc
prettyDistinctObject s = text "\"" <> (text . show) s <> text "\""

prettyLowerWord :: Token -> Doc
prettyLowerWord uw' = let uw = show uw' in text (toLower (head uw) : tail uw)

prettyUpperWord :: Token -> Doc
prettyUpperWord uw' = let uw = show uw' in text (toUpper (head uw) : tail uw)

orSign :: Doc
orSign = text "|"

andSign :: Doc
andSign = text "&"

applySign :: Doc
applySign = text "@"

arrowSign :: Doc
arrowSign = text ">"

starSign :: Doc
starSign = text "*"

plusSign :: Doc
plusSign = text "+"

sepBy :: [Doc] -> Doc -> Doc
sepBy ls s = case ls of
    (c : []) -> c
    (c : d) -> c <+> s <+> sepBy d s
    [] -> empty
