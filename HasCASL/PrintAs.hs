{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

printing data types of the abstract syntax
-}

module HasCASL.PrintAs where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.HToken
import HasCASL.MixPrint
import Common.Lib.Pretty
import Common.Id
import Common.Keywords
import Common.PPUtils
import Common.PrettyPrint
import Common.GlobalAnnotations(GlobalAnnos)
import Common.AS_Annotation(mapAnM)
import Data.List

-- | short cut for: if b then empty else d
noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

noNullPrint :: [a] -> Doc -> Doc
noNullPrint = noPrint . null

instance PrettyPrint Variance where
    printText0 _ = text . show

instance PrettyPrint a => PrettyPrint (AnyKind a) where
    printText0 ga knd = case knd of
        ClassKind ci -> printText0 ga ci
        FunKind v k1 k2 _ -> printText0 ga v <>
                          (case k1 of
                                  FunKind _ _ _ _ -> parens
                                  _ -> id) (printText0 ga k1)
                          <+> text funS
                          <+> printText0 ga k2

instance PrettyPrint TypePattern where
    printText0 ga tp = case tp of
        TypePattern name args _ -> printText0 ga name
                                 <> fcat (map (parens . printText0 ga) args)
        TypePatternToken t -> printText0 ga t
        MixfixTypePattern ts -> fsep (map (printText0 ga) ts)
        BracketTypePattern k l _ -> bracket k $ commaT_text ga l
        TypePatternArg t _ -> parens $ printText0 ga t

-- | put proper brackets around a document
bracket :: BracketKind -> Doc -> Doc
bracket b t = let (o,c) = getBrackets b in text o <> t <> text c

-- | print a 'Kind' plus a preceding colon (or nothing for 'star')
printKind :: GlobalAnnos -> Kind -> Doc
printKind ga k = if k == universe then empty else
                 printVarKind ga InVar (VarKind k)

-- | print the kind of a variable with its variance and a preceding colon
printVarKind :: GlobalAnnos -> Variance -> VarKind -> Doc
printVarKind ga e vk = case vk of
                    Downset t ->
                        space <> text lessS <+> printText0 ga t
                    VarKind k -> space <> colon <+>
                                 printText0 ga e <> printText0 ga k
                    MissingKind -> empty

data TypePrec = Outfix | Prefix | ProdInfix | FunInfix deriving (Eq, Ord)

parenPrec :: TypePrec -> (TypePrec, Type) -> Type
parenPrec p1 (p2, d) = if p2 < p1 then d else BracketType Parens [d] nullRange

toMixType :: Type -> (TypePrec, Type)
toMixType typ = case typ of
    ExpandedType t1 _ -> toMixType t1
    {- (Prefix, ExpandedType
                      (parenPrec Prefix $ toMixType t1)
                         $ parenPrec Prefix $ toMixType t2) -}
    BracketType k l ps -> (Outfix, BracketType k (map
                             (snd . toMixType) l) ps)
    KindedType t kind ps -> (Prefix, KindedType
                             (parenPrec Prefix $ toMixType t) kind ps)
    MixfixType ts -> (Prefix, MixfixType $ map (snd . toMixType) ts)
    _ -> let (topTy, tyArgs) = getTypeAppl typ in
      case topTy of
      TypeName name@(Id ts cs _) _k _i -> case tyArgs of
          [] -> (Outfix, topTy)
          [arg] -> let dArg = toMixType arg in
               case ts of
               [e1, e2, e3] | not (isPlace e1) && isPlace e2
                              && not (isPlace e3) && null cs ->
                   (Outfix, MixfixType [TypeToken e1, snd dArg, TypeToken e3])
               _ -> (Prefix, MixfixType [topTy, parenPrec Prefix dArg])
          [arg1, arg2] -> let dArg1 = toMixType arg1
                              dArg2 = toMixType arg2 in
               case ts of
               [e1, e2, e3] | isPlace e1 && not (isPlace e2)
                              && isPlace e3 && null cs ->
                    if tokStr e2 == prodS then
                      (ProdInfix, MixfixType [
                       parenPrec ProdInfix dArg1, TypeToken e2,
                       parenPrec ProdInfix dArg2])
                    else -- assume fun type
                      (FunInfix, MixfixType [
                       parenPrec FunInfix dArg1, TypeToken e2, snd dArg2])
               _ -> (Prefix, MixfixType [topTy, parenPrec Prefix dArg1,
                               parenPrec Prefix dArg2])
          _ -> if name == productId (length tyArgs) then
                (ProdInfix, MixfixType $ intersperse
                 (TypeToken $ mkSimpleId prodS) $
                          map (parenPrec ProdInfix . toMixType) tyArgs)
                else (Prefix, MixfixType $ topTy :
                            map (parenPrec Prefix . toMixType) tyArgs)
      _ | null tyArgs -> (Outfix, topTy)
      _ -> (Prefix, MixfixType $ parenPrec ProdInfix (toMixType topTy)
         : map (parenPrec Prefix . toMixType) tyArgs)

printType :: GlobalAnnos -> Type -> Doc
printType ga ty = case ty of
        TypeName name _ _ -> printText0 ga name
          -- if i == 0 then empty else text ("_v"++ show i)
        TypeAppl t1 t2 -> parens (printType ga t1) <>
                          parens (printType ga t2)
        ExpandedType t1 t2 -> printType ga t1 <> text asP <> printType ga t2
        TypeToken t -> printText0 ga t
        BracketType k l _ -> bracket k $ fsep $
                             punctuate comma $ map (printType ga) l
        KindedType t kind _ -> printType ga t
                                       <+> colon <+> printText0 ga kind
        MixfixType ts -> fsep $ map (printType ga) ts

instance PrettyPrint Type where
    printText0 ga = printType ga . snd . toMixType

-- no curried notation for bound variables
instance PrettyPrint TypeScheme where
    printText0 ga (TypeScheme vs t _) = let tdoc = printText0 ga t in
        if null vs then tdoc else
           hang (text forallS <+> semiT_text ga vs <+> text dotS) 2 tdoc

instance PrettyPrint Instance where
    printText0 _ i = case i of
        Instance -> space <> text instanceS
        Plain -> empty

instance PrettyPrint Partiality where
    printText0 _ p = case p of
        Partial -> text quMark
        Total -> empty

instance PrettyPrint Arrow where
    printText0 _ a = text $ show a

instance PrettyPrint Quantifier where
    printText0 _ q = text $ show q

instance PrettyPrint TypeQual where
    printText0 _ q = text $ show q

instance PrettyPrint Term where
    printText0 ga t = printTerm ga $ convTerm ga $ rmSomeTypes t

printTerm :: GlobalAnnos -> Term -> Doc
printTerm ga trm =
    let commaT = fsep . punctuate comma . map (printTerm ga)
    in case trm of
        QualVar vd -> parens $ text varS <+> printText0 ga vd
        QualOp br n t _ -> parens $ fsep [printText0 ga br, printText0 ga n,
                                colon, printText0 ga $
                                if isPred br then unPredTypeScheme t else t]
        ResolvedMixTerm n ts _ ->
            case ts of
            [] ->  printText0 ga n
            [t] -> printText0 ga n <> (case t of
                   TupleTerm _ _ -> id
                   BracketTerm _ _ _ -> id
                   QualVar _ -> id
                   QualOp _ _ _ _ -> id
                   ResolvedMixTerm _ [] _ -> (space <>)
                   TermToken _ -> (space <>)
                   _ -> parens) (printTerm ga t)
            _ -> printText0 ga n <> parens (commaT ts)
        ApplTerm t1 t2 _ ->
            hang (printTerm ga t1) 2 $ printTerm ga t2
        TupleTerm ts _ -> parens (commaT ts)
        TypedTerm t q typ _ ->
            fsep [printTerm ga t, printText0 ga q, printText0 ga typ]
        QuantifiedTerm q vs t _ -> hang (printText0 ga q <+> semiT_text ga vs)
                                   2 (text dotS <+> printTerm ga t)
        LambdaTerm ps q t _ -> hang (text lamS <+> (case ps of
            [p] -> printTerm ga p
            _ -> fcat $ map (parens . printTerm ga) ps))
            2 $ (case q of
                Partial -> text dotS
                Total -> text $ dotS ++ exMark) <+> printTerm ga t
        CaseTerm t es _  -> hang (fsep [text caseS, printText0 ga t, text ofS])
            4 $ vcat (punctuate (text " | ") $ map (printEq0 ga funS) es)
        LetTerm br es t _ ->
            let dt = printTerm ga t
                des = vcat $ punctuate semi $ map (printEq0 ga equalS) es
                in case br of
                Let -> hang (sep [text letS <+> des, text inS]) 3 dt
                Where -> hang (sep [dt, text whereS]) 6 des
                Program -> text programS <+> des
        TermToken t -> printText0 ga t
        MixTypeTerm q t _ -> printText0 ga q <+> printText0 ga t
        MixfixTerm ts -> fsep $ map (printTerm ga) ts
        BracketTerm k l _ -> bracket k $ commaT l
        AsPattern (VarDecl v _ _ _) p _ ->
            printText0 ga v <+> text asP <+> printTerm ga p

-- | print an equation with different symbols between 'Pattern' and 'Term'
printEq0 :: GlobalAnnos -> String -> ProgEq -> Doc
printEq0 ga s (ProgEq p t _) =
    hang (hang (printTerm ga p) 2 $ text s) 4 $ printTerm ga t

instance PrettyPrint VarDecl where
    printText0 ga (VarDecl v t _ _) = printText0 ga v <>
       case t of
       MixfixType [] -> empty
       _ -> space <> colon <+> printText0 ga t

instance PrettyPrint GenVarDecl where
    printText0 ga gvd = case gvd of
        GenVarDecl v -> printText0 ga v
        GenTypeVarDecl tv -> printText0 ga tv

instance PrettyPrint TypeArg where
    printText0 ga (TypeArg v e c _ _ _ _) =
        printText0 ga v <> printVarKind ga e c

-- | don't print an empty list and put parens around longer lists
printList0 :: (PrettyPrint a) => GlobalAnnos -> [a] -> Doc
printList0 ga l =  case l of
    []  -> empty
    [x] -> printText0 ga x
    _   -> parens $ commaT_text ga l

instance PrettyPrint InstOpId where
    printText0 ga (InstOpId n l _) = printText0 ga n <> noNullPrint l
                                     (brackets $ semiT_text ga l)

-- | print a 'TypeScheme' as a pseudo type
printPseudoType :: GlobalAnnos -> TypeScheme -> Doc
printPseudoType ga (TypeScheme l t _) = noNullPrint l (text lamS
    <+> (if null $ tail l then printText0 ga $ head l
         else fcat(map (parens . printText0 ga) l))
            <+> text dotS <> space) <> printText0 ga t

instance PrettyPrint BasicSpec where
    printText0 ga (BasicSpec l) = vcat (map (printText0 ga) l)

instance PrettyPrint ProgEq where
    printText0 ga (ProgEq p q ps) =
        printEq0 ga equalS $ ProgEq (convTerm ga p) (convTerm ga q) ps

instance PrettyPrint BasicItem where
    printText0 ga bi = case bi of
        SigItems s -> printText0 ga s
        ProgItems l _ -> noNullPrint l $ text programS <+> semiAnno_text ga l
        ClassItems i l _ -> noNullPrint l $ text classS <> printText0 ga i
                            <+> semiAnno_text ga l
        GenVarItems l _ -> noNullPrint l $ text varS <+> semiT_text ga l
        FreeDatatype l _ -> noNullPrint l $ text freeS <+> text typeS
                            <+> semiAnno_text ga l
        GenItems l _ -> noNullPrint l $ text generatedS
                        <+> braces (semiAnno_text ga l)
        AxiomItems vs fs _ -> (noNullPrint vs $ text forallS
                               <+> semiT_text ga vs)
                              $$ vcat (map ( \ x -> text dotS
                                             <+> printText0 ga x) fs)
        Internal l _ -> noNullPrint l $ text internalS
                        <+> braces (semiAnno_text ga l)

instance PrettyPrint OpBrand where
    printText0 _ b = text $ show b

instance PrettyPrint SigItems where
    printText0 ga si = case si of
        TypeItems i l _ -> noNullPrint l $ text typeS <> printText0 ga i
                           <+> semiAnno_text ga l
        OpItems b l _ -> noNullPrint l $ printText0 ga b <+> semiAnno_text ga
                         (if isPred b then concat $
                          mapAnM ((:[]) . mapOpItem) l else l)

instance PrettyPrint ClassItem where
    printText0 ga (ClassItem d l _) = printText0 ga d $$
                                   if null l then empty
                                      else braces (semiAnno_text ga l)

instance PrettyPrint ClassDecl where
    printText0 ga (ClassDecl l k _) = commaT_text ga l
                                      <+> text lessS <+> printText0 ga k

instance PrettyPrint Vars where
    printText0 ga vd = case vd of
        Var v -> printText0 ga v
        VarTuple vs _ -> parens $ commaT_text ga vs

instance PrettyPrint TypeItem where
    printText0 ga ti = case ti of
        TypeDecl l k _ -> if null l then error "printText0 TypeDecl" else
                          commaT_text ga l <> printKind ga k
        SubtypeDecl l t _ -> if null l then error "printText0 SubtypeDecl"
            else commaT_text ga l <+> text lessS <+> printText0 ga t
        IsoDecl l _ -> cat(punctuate (text " = ")
                                      (map (printText0 ga) l))
        SubtypeDefn p v t f _ -> printText0 ga p
                               <+> text equalS
                               <+> braces (printText0 ga v
                                           <+> colon
                                           <+> printText0 ga t
                                           <+> text dotS
                                           <+> printText0 ga f)
        AliasType p k t _ ->  (printText0 ga p <>
                                          case k of
                                          Nothing -> empty
                                          Just j -> space <> colon <+>
                                                   printText0 ga j)
                                       <+> text assignS
                                       <+> printPseudoType ga t
        Datatype t -> printText0 ga t

mapOpItem :: OpItem -> OpItem
mapOpItem oi = case oi of
    OpDecl l t as ps -> OpDecl l (unPredTypeScheme t) as ps
    OpDefn n ps s p t qs -> OpDefn n ps (unPredTypeScheme s) p t qs

instance PrettyPrint OpItem where
    printText0 ga oi = case oi of
        OpDecl l t attrs _ -> if null l then error "printText0 OpDecl" else
            commaT_text ga l <+> colon <+> (printText0 ga t
                 <> (if null attrs then empty else comma <> space)
                 <> commaT_text ga attrs)
        OpDefn n ps s p t _ -> hang
            (hang (printText0 ga n <> fcat (map (parens . semiT_text ga) ps))
                            2 (colon <> printText0 ga p
                            <+> printText0 ga s))
                            2 (text equalS
                               <+> printText0 ga t)

instance PrettyPrint BinOpAttr where
    printText0 _ a = text $ case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS

instance PrettyPrint OpAttr where
    printText0 ga oa = case oa of
        BinOpAttr a _ -> printText0 ga a
        UnitOpAttr t _ -> text unitS <+> printText0 ga t

instance PrettyPrint DatatypeDecl where
    printText0 ga (DatatypeDecl p k alts d _) = (printText0 ga p <>
                                               printKind ga k)
                                  <+> text defnS
                                  <+> vcat(punctuate (text " | ")
                                           (map (printText0 ga) alts))
                                  <+> case d of [] -> empty
                                                _ -> text derivingS
                                                          <+> commaT_text ga d

instance PrettyPrint Alternative where
    printText0 ga alt = case alt of
        Constructor n cs p _ ->
            printText0 ga n <+> fsep (map (parens . semiT_text ga) cs)
                       <> printText0 ga p
        Subtype l _ -> noNullPrint l $ text typeS <+> commaT_text ga l

instance PrettyPrint Component where
    printText0 ga sel = case sel of
        Selector n p t _ _ -> printText0 ga n
                              <+> colon <> printText0 ga p
                                      <+> printText0 ga t
        NoSelector t -> printText0 ga t

instance PrettyPrint OpId where
    printText0 ga (OpId n ts _) = printText0 ga n
                                  <+> noNullPrint ts
                                      (brackets $ commaT_text ga ts)

instance PrettyPrint Symb where
    printText0 ga (Symb i mt _) =
        printText0 ga i <> (case mt of Nothing -> empty
                                       Just (SymbType t) ->
                                          empty <+> colon <+>
                                            printText0 ga t)

instance PrettyPrint SymbItems where
    printText0 ga (SymbItems k syms _ _) =
        printSK k <> commaT_text ga syms

instance PrettyPrint SymbOrMap where
    printText0 ga (SymbOrMap s mt _) =
        printText0 ga s <> (case mt of Nothing -> empty
                                       Just t ->
                                          empty <+> text mapsTo <+>
                                            printText0 ga t)

instance PrettyPrint SymbMapItems where
    printText0 ga (SymbMapItems k syms _ _) =
        printSK k <> commaT_text ga syms

-- | print symbol kind
printSK :: SymbKind -> Doc
printSK k =
    case k of Implicit -> empty
              _ -> text (drop 3 $ show k) <> space
