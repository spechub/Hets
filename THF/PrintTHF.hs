{- |
Module      :  $Header$
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
--import Common.DocUtils

printTPTPTHF :: [TPTP_THF] -> Doc
printTPTPTHF [] = empty
printTPTPTHF (t : rt) = case t of
    TPTP_THF_Annotated_Formula _ _ _ _ -> printTHF t $++$ printTPTPTHF rt
    _                                   -> printTHF t $+$ printTPTPTHF rt


class PrintTHF a where
    printTHF :: a -> Doc

instance PrintTHF TPTP_THF where
    printTHF t = case t of
        TPTP_THF_Annotated_Formula n fr f a ->
            text "thf" <> parens (printTHF n <> comma
                <+> printTHF fr <> comma
                <+> printTHF f <> printTHF a)
            <> text "."
        TPTP_Include i                      -> printTHF i
        TPTP_Comment c                      -> printTHF c
        TPTP_Defined_Comment dc             -> printTHF dc
        TPTP_System_Comment sc              -> printTHF sc
        TPTP_Header h                       -> printHeader h

printHeader :: [Comment] -> Doc
printHeader (c : rc) = printTHF c $+$ printHeader rc
printHeader [] = empty

instance PrintTHF Comment where
    printTHF c = case c of
        Comment_Line s      -> text "%" <> text s
        Comment_Block sl    -> text "/*"
                $+$ printCommentBlock sl
                $+$ text "*/"

instance PrintTHF DefinedComment where
    printTHF dc = case dc of
        Defined_Comment_Line s      -> text "%$" <> text s
        Defined_Comment_Block sl    -> text "/*$"
                $+$ printCommentBlock sl
                $+$ text "*/"

instance PrintTHF SystemComment where
    printTHF sc = case sc of
        System_Comment_Line s   -> text "%$$" <> text s
        System_Comment_Block sl -> text "/*$$"
                $+$ printCommentBlock sl
                $+$ text "*/"

printCommentBlock :: [String] -> Doc
printCommentBlock []        = empty
printCommentBlock (s : rt)  = text s $+$ printCommentBlock rt

instance PrintTHF Include where
    printTHF (I_Include fn nl) = text "include" <> parens (printFileName fn
        <> maybe empty (\c -> comma <+> printNameList c) nl) <> text "."

instance PrintTHF Annotations where
    printTHF a = case a of
        Annotations s o -> comma <+> printTHF s <> printOptionalInfo o
        Null            -> empty

instance PrintTHF FormulaRole where
    printTHF fr = text $ map toLower (show fr)

instance PrintTHF THFFormula where
    printTHF f = case f of
        TF_THF_Logic_Formula lf -> printTHF lf
        TF_THF_Sequent s        -> printTHF s
        T0F_THF_Typed_Const tc  -> printTHF tc

instance PrintTHF THFLogicFormula where
    printTHF lf = case lf of
        TLF_THF_Binary_Formula bf   -> printTHF bf
        TLF_THF_Unitary_Formula uf  -> printTHF uf
        TLF_THF_Type_Formula tf     -> printTHF tf
        TLF_THF_Sub_Type st         -> printTHF st

instance PrintTHF THFBinaryFormula where
    printTHF bf = case bf of
        TBF_THF_Binary_Tuple bt         -> printTHF bt
        TBF_THF_Binary_Type bt          -> printTHF bt
        TBF_THF_Binary_Pair uf1 pc uf2  ->
            printTHF uf1 <+> printTHF pc <+> printTHF uf2

instance PrintTHF THFBinaryTuple where
    printTHF bt = case bt of
        TBT_THF_Or_Formula ufl      -> sepBy (map printTHF ufl) orSign
        TBT_THF_And_Formula ufl     -> sepBy (map printTHF ufl) andSign
        TBT_THF_Apply_Formula ufl   -> sepBy (map printTHF ufl) applySign

instance PrintTHF THFUnitaryFormula where
    printTHF tuf = case tuf of
        TUF_THF_Quantified_Formula qf   -> printTHF qf
        TUF_THF_Unary_Formula uc lf     -> printTHF uc <+> parens (printTHF lf)
        TUF_THF_Atom a                  -> printTHF a
        TUF_THF_Tuple t                 -> printTHFTuple t
        TUF_THF_Let dvl uf              ->
            text ":=" <+> brackets (sepByCommas (map printTHF dvl))
            <+> text ":" <+> printTHF uf
        TUF_THF_Conditional lf1 lf2 lf3 ->
            text "$itef" <> parens (printTHF lf1
            <> comma <+> printTHF lf2
            <> comma <+> printTHF lf3)
        TUF_THF_Logic_Formula_Par l     -> parens (printTHF l)
        T0UF_THF_Abstraction vl uf      -> text "^" <+>
            brackets (printTHFVariableList vl) <+> text ":" <+> printTHF uf

instance PrintTHF THFQuantifiedFormula where
    printTHF qf = case qf of
        TQF_THF_Quantified_Formula tq vl uf -> printTHF tq <+>
            brackets (printTHFVariableList vl) <+> text ":" <+> printTHF uf
        T0QF_THF_Quantified_Var q vl uf     -> printTHF q <+>
            brackets (printTHFVariableList vl) <+> text ":" <+> printTHF uf
        T0QF_THF_Quantified_Novar tq uf     ->
            printTHF tq <+> parens (printTHF uf)

printTHFVariableList :: THFVariableList -> Doc
printTHFVariableList vl = sepByCommas (map printTHF vl)

instance PrintTHF THFVariable where
    printTHF v = case v of
        TV_THF_Typed_Variable va tlt -> printVariable va
            <+> text ":" <+> printTHF tlt
        TV_Variable var             -> printVariable var

instance PrintTHF THFTypedConst where
    printTHF ttc = case ttc of
        T0TC_Typed_Const c tlt      -> printConstant c <+> text ":"
            <+> printTHF tlt
        T0TC_THF_TypedConst_Par tc  -> parens (printTHF tc)

instance PrintTHF THFTypeFormula where
    printTHF ttf = case ttf of
        TTF_THF_Type_Formula tf tlt -> printTHF tf <+> text ":" <+> printTHF tlt
        TTF_THF_Typed_Const c tlt   -> printConstant c <+> text ":"
            <+> printTHF tlt

instance PrintTHF THFTypeableFormula where
    printTHF tbf = case tbf of
        TTyF_THF_Atom a             -> printTHF a
        TTyF_THF_Tuple t            -> printTHFTuple t
        TTyF_THF_Logic_Formula lf   -> parens $ printTHF lf

instance PrintTHF THFSubType where
    printTHF (TST_THF_Sub_Type c1 c2) =
        printConstant c1 <+> text "<<" <+> printConstant c2

instance PrintTHF THFTopLevelType where
    printTHF tlt = case tlt of
        TTLT_THF_Logic_Formula lf   -> printTHF lf
        T0TLT_Constant c            -> printConstant c
        T0TLT_Variable v            -> printVariable v
        T0TLT_Defined_Type dt       -> printTHF dt
        T0TLT_System_Type st        -> printSystemType st
        T0TLT_THF_Binary_Type bt    -> printTHF bt

instance PrintTHF THFUnitaryType where
    printTHF ut = case ut of
        TUT_THF_Unitary_Formula uf  -> printTHF uf
        T0UT_Constant c             -> printConstant c
        T0UT_Variable v             -> printVariable v
        T0UT_Defined_Type dt        -> printTHF dt
        T0UT_System_Type st         -> printSystemType st
        T0UT_THF_Binary_Type_Par bt -> parens (printTHF bt)

instance PrintTHF THFBinaryType where
    printTHF tbt = case tbt of
        TBT_THF_Mapping_Type utl    -> sepBy (map printTHF utl) arrowSign
        TBT_THF_Xprod_Type utl      -> sepBy (map printTHF utl) starSign
        TBT_THF_Union_Type utl      -> sepBy (map printTHF utl) plusSign
        T0BT_THF_Binary_Type_Par bt -> parens (printTHF bt)

instance PrintTHF THFAtom where
    printTHF a = case a of
        TA_Term t                   -> printTHF t
        TA_THF_Conn_Term ct         -> printTHF ct
        TA_Defined_Type dt          -> printTHF dt
        TA_Defined_Plain_Formula dp -> printTHF dp
        TA_System_Type st           -> printSystemType st
        TA_System_Atomic_Formula st -> printTHF st
        T0A_Constant c              -> printConstant c
        T0A_Defined_Constant dc     -> printAtomicDefinedWord dc
        T0A_System_Constant sc      -> printAtomicSystemWord sc
        T0A_Variable v              -> printVariable v

printTHFTuple :: THFTuple -> Doc
printTHFTuple ufl = brackets $ sepByCommas (map printTHF ufl)

instance PrintTHF THFDefinedVar where
    printTHF dv = case dv of
        TDV_THF_Defined_Var v lf        ->
            printTHF v <+> text ":=" <+> printTHF lf
        TDV_THF_Defined_Var_Par d -> parens (printTHF d)

instance PrintTHF THFSequent where
    printTHF (TS_THF_Sequent_Par s) = parens $ printTHF s
    printTHF (TS_THF_Sequent t1 t2) =
        printTHFTuple t1 <+> text "-->" <+> printTHFTuple t2

instance PrintTHF THFConnTerm where
    printTHF ct = case ct of
        TCT_THF_Pair_Connective pc  -> printTHF pc
        TCT_Assoc_Connective ac     -> printTHF ac
        TCT_THF_Unary_Connective uc -> printTHF uc
        T0CT_THF_Quantifier q       -> printTHF q

instance PrintTHF THFQuantifier where
    printTHF q = case q of
        TQ_ForAll                   -> text "!"
        TQ_Exists                   -> text "?"
        TQ_Lambda_Binder            -> text "^"
        TQ_Dependent_Product        -> text "!>"
        TQ_Dependent_Sum            -> text "?*"
        TQ_Indefinite_Description   -> text "@+"
        TQ_Definite_Description     -> text "@-"
        T0Q_PiForAll                -> text "!!"
        T0Q_SigmaExists             -> text "??"

instance PrintTHF Quantifier where
    printTHF q = case q of
        T0Q_ForAll  -> text "!"
        T0Q_Exists  -> text "?"

instance PrintTHF THFPairConnective where
    printTHF pc = case pc of
        Infix_Equality      -> text "="
        Infix_Inequality    -> text "!="
        Equivalent          -> text "<=>"
        Implication         -> text "=>"
        IF                  -> text "<="
        XOR                 -> text "<~>"
        NOR                 -> text "~|"
        NAND                -> text "~&"

instance PrintTHF THFUnaryConnective where
    printTHF uc = case uc of
        Negation    -> text "~"
        PiForAll    -> text "!!"
        SigmaExists -> text "??"

instance PrintTHF AssocConnective where
    printTHF AND    = text "&"
    printTHF OR     = text "|"

instance PrintTHF DefinedType where
    printTHF dt = text $ "$" ++ drop 3 (show dt)

printSystemType :: SystemType -> Doc
printSystemType = printAtomicSystemWord

instance PrintTHF DefinedPlainFormula where
    printTHF dpf = case dpf of
        DPF_Defined_Prop dp         -> printTHF dp
        DPF_Defined_Formula dp a    -> printTHF dp <> parens (printArguments a)

instance PrintTHF DefinedProp where
    printTHF DP_True    = text "$true"
    printTHF DP_False   = text "$false"

instance PrintTHF DefinedPred where
    printTHF dp = text $ "$" ++ map toLower (show dp)

instance PrintTHF Term where
    printTHF t = case t of
        T_Function_Term ft  -> printTHF ft
        T_Variable v        -> printVariable v

instance PrintTHF FunctionTerm where
    printTHF ft = case ft of
        FT_Plain_Term pt    -> printTHF pt
        FT_Defined_Term dt  -> printTHF dt
        FT_System_Term st   -> printTHF st

instance PrintTHF PlainTerm where
    printTHF pt = case pt of
        PT_Constant c       -> printConstant c
        PT_Plain_Term f a   -> printTPTPFunctor f <> parens (printArguments a)

printConstant :: Constant -> Doc
printConstant = printTPTPFunctor

printTPTPFunctor :: TPTPFunctor -> Doc
printTPTPFunctor = printTHF

instance PrintTHF DefinedTerm where
    printTHF dt = case dt of
        DT_Defined_Atom da          -> printTHF da
        DT_Defined_Atomic_Term dpt  -> printTHF dpt

instance PrintTHF DefinedAtom where
    printTHF da = case da of
        DA_Number n             -> printTHF n
        DA_Distinct_Object dio  -> printDistinctObject dio

instance PrintTHF DefinedPlainTerm where
    printTHF dpt = case dpt of
        DPT_Defined_Constant df     -> printTHF df
        DPT_Defined_Function df a   -> printTHF df <> parens (printArguments a)

instance PrintTHF DefinedFunctor where
    printTHF df = text $ "$" ++ map toLower (show df)

instance PrintTHF SystemTerm where
    printTHF st = case st of
        ST_System_Constant sf   -> printSystemFunctor sf
        ST_System_Term sf a     -> printSystemFunctor sf
            <> parens (printArguments a)

printSystemFunctor :: SystemFunctor -> Doc
printSystemFunctor = printAtomicSystemWord

printVariable :: Variable -> Doc
printVariable = text

printArguments :: Arguments -> Doc
printArguments = sepByCommas . map printTHF

instance PrintTHF PrincipalSymbol where
    printTHF ps = case ps of
        PS_Functor f    -> printTPTPFunctor f
        PS_Variable v   -> printVariable v

instance PrintTHF Source where
    printTHF s = case s of
        S_Dag_Source ds         -> printTHF ds
        S_Internal_Source it oi -> text "introduced" <> parens (
            printTHF it <> printOptionalInfo oi)
        S_External_Source es    -> printTHF es
        S_Sources ss            -> sepByCommas (map printTHF ss)
        S_Unknown               -> text "unknown"

instance PrintTHF DagSource where
    printTHF ds = case ds of
        DS_Name n                       -> printTHF n
        DS_Inference_Record aw ui pl    -> text "inference"
            <> parens (printTHF aw <> comma <+> printUsefulInfo ui
            <> comma <+> brackets (sepByCommas (map printTHF pl)))

instance PrintTHF ParentInfo where
    printTHF (PI_Parent_Info s mgl) =
        let gl = maybe empty (\c -> text ":" <> printGeneralList c) mgl
        in printTHF s <> gl

instance PrintTHF IntroType where
    printTHF it = text (drop 3 (show it))

instance PrintTHF ExternalSource where
    printTHF es = case es of
        ES_File_Source fs       -> printTHF fs
        ES_Theory tn oi         -> text "theory" <> parens (
            printTHF tn <> printOptionalInfo oi)
        ES_Creator_Source aw oi -> text "creator" <> parens (
            printTHF aw <> printOptionalInfo oi)

instance PrintTHF FileSource where
    printTHF (FS_File fn mn) =
        let n = maybe empty (\c -> comma <+> printTHF c) mn
        in text "file" <> parens (printFileName fn <> n)

instance PrintTHF TheoryName where
    printTHF tn = text $ map toLower (show tn)

printOptionalInfo :: OptionalInfo -> Doc
printOptionalInfo = maybe empty (\ui -> comma <+> printUsefulInfo ui)

printUsefulInfo :: UsefulInfo -> Doc
printUsefulInfo = brackets . sepByCommas . map printTHF

instance PrintTHF InfoItem where
    printTHF ii = case ii of
        II_Formula_Item fi      -> printTHF fi
        II_Inference_Item infi  -> printTHF infi
        II_General_Function gf  -> printTHF gf

instance PrintTHF FormulaItem where
    printTHF fi = case fi of
        FI_Description_Item aw  -> text "description" <> parens (printTHF aw)
        FI_Iquote_Item aw       -> text "iquote" <> parens (printTHF aw)

instance PrintTHF InferenceItem where
    printTHF ii = case ii of
        II_Inference_Status is      -> printTHF is
        II_Assumptions_Record nl    -> text "assumptions"
            <> parens (brackets (printNameList nl))
        II_New_Symbol_Record aw psl -> text "new_symbols" <> parens (printTHF aw
            <> comma <+> brackets (sepByCommas (map printTHF psl)))
        II_Refutation fs            -> text "refutation" <> parens (printTHF fs)

instance PrintTHF InferenceStatus where
    printTHF is = case is of
        IS_Status s                     -> text "status" <> parens (printTHF s)
        IS_Inference_Info aw1 aw2 gl    -> printTHF aw1 <> parens (printTHF aw2
            <> comma <+> printGeneralList gl)

instance PrintTHF StatusValue where
    printTHF sv = text $ map toLower (show sv)

printNameList :: NameList -> Doc
printNameList = sepByCommas . map printTHF

instance PrintTHF GeneralTerm where
    printTHF gt = case gt of
        GT_General_Data gd          -> printTHF gd
        GT_General_Data_Term gd gt1 -> printTHF gd <+> text ":" <+> printTHF gt1
        GT_General_List gl          -> printGeneralList gl

instance PrintTHF GeneralData where
    printTHF gd = case gd of
        GD_Atomic_Word aw       -> printTHF aw
        GD_General_Function gf  -> printTHF gf
        GD_Variable v           -> printVariable v
        GD_Number n             -> printTHF n
        GD_Distinct_Object dio  -> printDistinctObject dio
        GD_Formula_Data fd      -> printTHF fd
        GD_Bind v fd            -> text "bind" <> parens (
            printVariable v <> comma <+> printTHF fd)

instance PrintTHF GeneralFunction where
    printTHF (GF_General_Function aw gts) =
        printTHF aw <> parens (printGeneralTerms gts)

instance PrintTHF FormulaData where
    printTHF (THF_Formula thff) = text "$thf" <> parens (printTHF thff)

printGeneralList :: GeneralList -> Doc
printGeneralList = brackets . printGeneralTerms

printGeneralTerms :: GeneralTerms -> Doc
printGeneralTerms = sepByCommas . map printTHF

instance PrintTHF Name where
    printTHF n = case n of
        N_Atomic_Word a         -> printTHF a
        N_Integer s             -> text s
        T0N_Unsigned_Integer s  -> text s

instance PrintTHF AtomicWord where
    printTHF a = case a of
        A_Single_Quoted s   -> printSingleQuoted s
        A_Lower_Word l      -> text l

printAtomicSystemWord :: AtomicSystemWord -> Doc
printAtomicSystemWord asw = text ("$$" ++ asw)

printAtomicDefinedWord :: AtomicDefinedWord -> Doc
printAtomicDefinedWord adw = text ("$" ++ adw)

instance PrintTHF Number where
    printTHF n = case n of
        Num_Integer i   -> text i
        Num_Rational ra -> text ra
        Num_Real re     -> text re

printFileName :: FileName -> Doc
printFileName = printSingleQuoted

printSingleQuoted :: SingleQuoted -> Doc
printSingleQuoted s = text "\'" <> text s <> text "\'"

printDistinctObject :: DistinctObject -> Doc
printDistinctObject s = text "\"" <> text s <> text "\""

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
    (c : [])    -> c
    (c : d)     -> c <+> s <+> sepBy d s
    []          -> empty
