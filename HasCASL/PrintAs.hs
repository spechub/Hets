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
import HasCASL.FoldTerm
import HasCASL.Builtin
import Common.PrettyPrint
import Common.PPUtils()
import Common.Id
import Common.Keywords
import Common.Doc
import Common.AS_Annotation
import Data.List

instance PrettyPrint BasicSpec where
    printText0 ga = toText (addBuiltins ga) . rmTopKey . pretty

instance PrintLaTeX BasicSpec where
    printLatex0 ga = toLatex (addBuiltins ga) . pretty

instance PrettyPrint BasicItem where
    printText0 ga = toText ga . rmTopKey . pretty

instance PrettyPrint Type where
    printText0 ga = toText ga . pretty

instance PrettyPrint TypePattern where
    printText0 ga = toText ga . pretty

instance PrettyPrint Term where
    printText0 ga = toText (addBuiltins ga) . pretty

instance Pretty a => PrettyPrint (AnyKind a) where
    printText0 ga = toText ga . pretty

-- | short cut for: if b then empty else d
noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

noNullPrint :: [a] -> Doc -> Doc
noNullPrint = noPrint . null

commaDs :: Pretty a => [a] -> Doc
commaDs = fsep . punctuate comma . map pretty

semiDs :: Pretty a => [a] -> Doc
semiDs = fsep . punctuate semi . map pretty

semiAnnoted :: Pretty a => [Annoted a] -> Doc
semiAnnoted = semiAnnos pretty

instance Pretty Variance where
    pretty = idDoc . simpleIdToId . mkSimpleId . show

instance Pretty a => Pretty (AnyKind a) where
    pretty knd = case knd of
        ClassKind ci -> pretty ci
        FunKind v k1 k2 _ -> pretty v <>
                          (case k1 of
                                  FunKind _ _ _ _ -> parens
                                  _ -> id) (pretty k1)
                          <+> funArrow
                          <+> pretty k2

instance Pretty TypePattern where
    pretty tp = case tp of
        TypePattern name args _ -> pretty name
                                 <> fcat (map (parens . pretty) args)
        TypePatternToken t -> pretty t
        MixfixTypePattern ts -> fsep (map (pretty) ts)
        BracketTypePattern k l _ -> bracket k $ commaDs l
        TypePatternArg t _ -> parens $ pretty t

-- | put proper brackets around a document
bracket :: BracketKind -> Doc -> Doc
bracket b = case b of
              Parens -> parens
              Squares -> brackets
              Braces -> specBraces
              NoBrackets -> id

-- | print a 'Kind' plus a preceding colon (or nothing)
printKind :: Kind -> Doc
printKind k = if k == universe then empty else
                 printVarKind InVar (VarKind k)

-- | print the kind of a variable with its variance and a preceding colon
printVarKind :: Variance -> VarKind -> Doc
printVarKind e vk = case vk of
                    Downset t ->
                        space <> less <+> pretty t
                    VarKind k -> space <> colon <+>
                                 pretty e <> pretty k
                    MissingKind -> empty

data TypePrec = Outfix | Prefix | ProdInfix | FunInfix deriving (Eq, Ord)

parenPrec :: TypePrec -> (TypePrec, Doc) -> Doc
parenPrec p1 (p2, d) = if p2 < p1 then d else parens d

toMixType :: Type -> (TypePrec, Doc)
toMixType typ = case typ of
    ExpandedType t1 _ -> toMixType t1
    {- (Prefix, ExpandedType
                      (parenPrec Prefix $ toMixType t1)
                         $ parenPrec Prefix $ toMixType t2) -}
    BracketType k l _ -> (Outfix, bracket k $ fsep $ punctuate comma $ map
                             (snd . toMixType) l)
    KindedType t kind _ -> (Prefix,
               fsep [parenPrec Prefix $ toMixType t, colon, pretty kind])
    MixfixType ts -> (Prefix, fsep $ map (snd . toMixType) ts)
    _ -> let (topTy, tyArgs) = getTypeAppl typ in
      case topTy of
      TypeName name@(Id ts cs _) _k _i -> let topDoc = pretty name in
        case tyArgs of
          [] -> (Outfix, pretty name)
          [arg] -> let dArg = toMixType arg in
               case ts of
               [e1, e2, e3] | not (isPlace e1) && isPlace e2
                              && not (isPlace e3) && null cs ->
                   (Outfix, fsep [pretty e1, snd dArg, pretty e3])
               _ -> (Prefix, fsep [topDoc, parenPrec Prefix dArg])
          [arg1, arg2] -> let dArg1 = toMixType arg1
                              dArg2 = toMixType arg2 in
               case ts of
               [e1, e2, e3] | isPlace e1 && not (isPlace e2)
                              && isPlace e3 && null cs ->
                    if tokStr e2 == prodS then
                      (ProdInfix, fsep [
                       parenPrec ProdInfix dArg1, cross,
                       parenPrec ProdInfix dArg2])
                    else -- assume fun type
                      (FunInfix, fsep [
                       parenPrec FunInfix dArg1, pretty e2, snd dArg2])
               _ -> (Prefix, fsep [topDoc, parenPrec Prefix dArg1,
                               parenPrec Prefix dArg2])
          _ -> if name == productId (length tyArgs) then
                (ProdInfix, fsep $ punctuate (space <> cross) $
                          map (parenPrec ProdInfix . toMixType) tyArgs)
                else (Prefix, fsep $ topDoc :
                            map (parenPrec Prefix . toMixType) tyArgs)
      _ | null tyArgs -> (Outfix, printType topTy)
      _ -> (Prefix, fsep $ parenPrec ProdInfix (toMixType topTy)
         : map (parenPrec Prefix . toMixType) tyArgs)

printType :: Type -> Doc
printType ty = case ty of
        TypeName name _ _ -> pretty name
          -- if i == 0 then empty else text ("_v"++ show i)
        TypeAppl t1 t2 -> fcat [parens (printType t1),
                                parens (printType t2)]
        ExpandedType t1 t2 -> printType t1 <> text asP <> printType t2
        TypeToken t -> pretty t
        BracketType k l _ -> bracket k $ fsep $
                             punctuate comma $ map (printType) l
        KindedType t kind _ -> printType t
                                       <+> colon <+> pretty kind
        MixfixType ts -> fsep $ map printType ts

instance Pretty Type where
    pretty = snd . toMixType

-- no curried notation for bound variables
instance Pretty TypeScheme where
    pretty (TypeScheme vs t _) = let tdoc = pretty t in
        if null vs then tdoc else
           fsep [forallDoc, semiDs vs, bullet, tdoc]

instance Pretty Instance where
    pretty i = case i of
        Instance -> space <> keyword instanceS
        Plain -> empty

instance Pretty Partiality where
    pretty p = case p of
        Partial -> text quMark
        Total -> empty

instance Pretty Quantifier where
    pretty q = case q of
        Universal -> forallDoc
        Existential -> exists
        Unique -> unique

instance Pretty TypeQual where
    pretty q = case q of
        OfType -> colon
        AsType -> text asS
        InType -> inDoc
        Inferred -> colon

instance Pretty Term where
    pretty = changeGlobalAnnos addBuiltins . printTerm . rmSomeTypes

isSimpleTerm :: Term -> Bool
isSimpleTerm trm = case trm of
    QualVar _ -> True
    QualOp _ _ _ _ -> True
    ResolvedMixTerm _ _ _ -> True
    ApplTerm _ _ _ -> True
    TupleTerm _ _ -> True
    TermToken _ -> True
    BracketTerm _ _ _ -> True
    _ -> False

parenTermDoc :: Term -> Doc -> Doc
parenTermDoc trm = if isSimpleTerm trm then id else parens

printTermRec :: FoldRec Doc (Doc, Doc)
printTermRec = let commaT = fsep . punctuate comma in FoldRec
    { foldQualVar = \ _ vd -> parens $ keyword varS <+> pretty vd
    , foldQualOp = \ _ br n t _ ->
          parens $ fsep [pretty br, pretty n, colon, pretty $
                         if isPred br then unPredTypeScheme t else t]
    , foldResolvedMixTerm = \ (ResolvedMixTerm _ os _) n ts _ ->
          if placeCount n == length ts || null ts then
          idApplDoc n $ zipWith parenTermDoc os ts
          else idApplDoc applId [idDoc n, parens $ commaT ts]
    , foldApplTerm = \ (ApplTerm o1 o2 _) t1 t2 _ ->
        case (o1, o2) of
          (ResolvedMixTerm n [] _, TupleTerm ts _)
              | placeCount n == length ts ->
                  idApplDoc n $ zipWith parenTermDoc ts $ map printTerm ts
          (ResolvedMixTerm n [] _, _) | placeCount n == 1 ->
              idApplDoc n [parenTermDoc o2 t2]
          _ -> idApplDoc applId [parenTermDoc o1 t1, parenTermDoc o2 t2]
     , foldTupleTerm = \ _ ts _ -> parens $ commaT ts
     , foldTypedTerm = \ _ t q typ _ -> fsep [t, pretty q, pretty typ]
     , foldQuantifiedTerm = \ _ q vs t _ ->
           fsep [pretty q, semiDs vs, bullet, t]
     , foldLambdaTerm = \ _ ps q t _ ->
            fsep [ lambda
                 , case ps of
                      [p] -> p
                      _ -> fcat $ map parens ps
                 , case q of
                     Partial -> bullet
                     Total -> bullet <> text exMark
                 , t]
     , foldCaseTerm = \ _ t es _  ->
            fsep [text caseS, t, text ofS,
                  vcat $ punctuate (space <> bar <> space) $
                       map (printEq0 funArrow) es]
     , foldLetTerm = \ _ br es t _ ->
            let des = vcat $ punctuate semi $ map (printEq0 equals) es
                in case br of
                Let -> fsep [sep [text letS <+> des, text inS], t]
                Where -> fsep [sep [t, text whereS], des]
                Program -> text programS <+> des
     , foldTermToken = \ _ t -> pretty t
     , foldMixTypeTerm = \ _ q t _ -> pretty q <+> pretty t
     , foldMixfixTerm = \ _ ts -> fsep ts
     , foldBracketTerm = \ _ k l _ -> bracket k $ commaT l
     , foldAsPattern = \ _ (VarDecl v _ _ _) p _ -> pretty v <+> text asP <+> p
     , foldProgEq = \ _ p t _ -> (p, t)
    }

printTerm :: Term -> Doc
printTerm = foldTerm printTermRec

rmTypeRec :: MapRec
rmTypeRec = mapRec
    { -- foldQualVar = \ _ (VarDecl v _ _ ps) -> ResolvedMixTerm v [] ps
      foldQualOp = \ t _ (InstOpId i _ _) _ ps ->
                   if elem i $ map fst bList then
                     ResolvedMixTerm i [] ps else t
    , foldTypedTerm = \ _ nt q ty ps ->
           case q of
           Inferred -> nt
           _ -> case nt of
               TypedTerm _ oq oty _ | oty == ty || oq == InType -> nt
               QualVar (VarDecl _ oty _ _) | oty == ty -> nt
               _ -> TypedTerm nt q ty ps
    }

rmSomeTypes :: Term -> Term
rmSomeTypes = foldTerm rmTypeRec

-- | print an equation with different symbols between 'Pattern' and 'Term'
printEq0 :: Doc -> (Doc, Doc) -> Doc
printEq0 s (p, t) = fsep [p, s, t]

instance Pretty VarDecl where
    pretty (VarDecl v t _ _) = pretty v <>
       case t of
       MixfixType [] -> empty
       _ -> space <> colon <+> pretty t

instance Pretty GenVarDecl where
    pretty gvd = case gvd of
        GenVarDecl v -> pretty v
        GenTypeVarDecl tv -> pretty tv

instance Pretty TypeArg where
    pretty (TypeArg v e c _ _ _ _) =
        pretty v <> printVarKind e c

-- | don't print an empty list and put parens around longer lists
printList0 :: (Pretty a) => [a] -> Doc
printList0 l =  case l of
    []  -> empty
    [x] -> pretty x
    _   -> parens $ commaDs l

instance Pretty InstOpId where
    pretty (InstOpId n l _) = pretty n <> noNullPrint l
                                     (brackets $ semiDs l)

-- | print a 'TypeScheme' as a pseudo type
printPseudoType :: TypeScheme -> Doc
printPseudoType (TypeScheme l t _) = noNullPrint l (lambda
    <+> (if null $ tail l then pretty $ head l
         else fcat(map (parens . pretty) l))
            <+> bullet <> space) <> pretty t

instance Pretty BasicSpec where
    pretty (BasicSpec l) = vcat (map (pretty) l)

instance Pretty ProgEq where
    pretty = printEq0 equals . foldEq printTermRec

instance Pretty BasicItem where
    pretty bi = case bi of
        SigItems s -> pretty s
        ProgItems l _ -> noNullPrint l $ keyword programS <+> semiAnnoted l
        ClassItems i l _ -> noNullPrint l $ topKey classS <> pretty i
                            <+> semiAnnoted l
        GenVarItems l _ -> noNullPrint l $ topKey varS <+> semiDs l
        FreeDatatype l _ -> noNullPrint l $ keyword freeS <+> keyword typeS
                            <+> semiAnnoted l
        GenItems l _ -> noNullPrint l $ keyword generatedS
                        <+> specBraces (semiAnnoted l)
        AxiomItems vs fs _ ->
            vcat $ (if null vs then [] else
                    [forallDoc <+> semiDs vs])
                  ++ (map ( \ x -> bullet <+> pretty x) fs)
        Internal l _ -> noNullPrint l $ keyword internalS
                        <+> specBraces (semiAnnoted l)

instance Pretty OpBrand where
    pretty b = keyword $ show b

instance Pretty SigItems where
    pretty si = case si of
        TypeItems i l _ -> noNullPrint l $ topKey typeS <> pretty i
                           <+> semiAnnoted l
        OpItems b l _ -> noNullPrint l $ topKey (show b) <+> semiAnnoted
                         (if isPred b then concat $
                          mapAnM ((:[]) . mapOpItem) l else l)

instance Pretty ClassItem where
    pretty (ClassItem d l _) = pretty d $+$
                                   if null l then empty
                                      else specBraces (semiAnnoted l)

instance Pretty ClassDecl where
    pretty (ClassDecl l k _) = fsep [commaDs l, less, pretty k]

instance Pretty Vars where
    pretty vd = case vd of
        Var v -> pretty v
        VarTuple vs _ -> parens $ commaDs vs

instance Pretty TypeItem where
    pretty ti = case ti of
        TypeDecl l k _ -> if null l then error "pretty TypeDecl" else
                          commaDs l <> printKind k
        SubtypeDecl l t _ -> if null l then error "pretty SubtypeDecl"
            else fsep [commaDs l, less, pretty t]
        IsoDecl l _ -> fsep $ punctuate (space <> equals) $ map pretty l
        SubtypeDefn p v t f _ ->
            fsep [pretty p, equals,
                  specBraces $ fsep
                  [pretty v, colon, pretty t, bullet, pretty f]]
        AliasType p k t _ ->
            fsep $ pretty p : (case k of
                     Nothing -> []
                     Just j -> [colon, pretty j])
                  ++ [text assignS, printPseudoType t]
        Datatype t -> pretty t

mapOpItem :: OpItem -> OpItem
mapOpItem oi = case oi of
    OpDecl l t as ps -> OpDecl l (unPredTypeScheme t) as ps
    OpDefn n ps s p t qs -> OpDefn n ps (unPredTypeScheme s) p t qs

instance Pretty OpItem where
    pretty oi = case oi of
        OpDecl l t attrs _ -> if null l then error "pretty OpDecl" else
            commaDs l <+> colon <+> (pretty t
                 <> (if null attrs then empty else comma <> space)
                 <> commaDs attrs)
        OpDefn n ps s p t _ ->
            fsep [fcat $ pretty n : (map (parens . semiDs) ps)
                 , colon <> pretty p, pretty s, equals, pretty t]

instance Pretty BinOpAttr where
    pretty a = text $ case a of
        Assoc -> assocS
        Comm -> commS
        Idem -> idemS

instance Pretty OpAttr where
    pretty oa = case oa of
        BinOpAttr a _ -> pretty a
        UnitOpAttr t _ -> text unitS <+> pretty t

instance Pretty DatatypeDecl where
    pretty (DatatypeDecl p k alts d _) = (pretty p <> printKind k)
                                  <+> defn
                                  <+> vcat(punctuate (space <> bar <> space)
                                           $ map pretty alts)
                                  <+> case d of [] -> empty
                                                _ -> keyword derivingS
                                                          <+> commaDs d

instance Pretty Alternative where
    pretty alt = case alt of
        Constructor n cs p _ ->
            pretty n <+> fsep (map (parens . semiDs) cs)
                       <> pretty p
        Subtype l _ -> noNullPrint l $ text typeS <+> commaDs l

instance Pretty Component where
    pretty sel = case sel of
        Selector n p t _ _ -> pretty n
                              <+> colon <> pretty p
                                      <+> pretty t
        NoSelector t -> pretty t

instance Pretty OpId where
    pretty (OpId n ts _) = pretty n
                                  <+> noNullPrint ts
                                      (brackets $ commaDs ts)

instance Pretty Symb where
    pretty (Symb i mt _) =
        pretty i <> (case mt of
                       Nothing -> empty
                       Just (SymbType t) ->
                           empty <+> colon <+> pretty t)

instance Pretty SymbItems where
    pretty (SymbItems k syms _ _) =
        printSK k <> commaDs syms

instance Pretty SymbOrMap where
    pretty (SymbOrMap s mt _) =
        pretty s <> (case mt of
                       Nothing -> empty
                       Just t ->
                           empty <+> mapsto <+> pretty t)

instance Pretty SymbMapItems where
    pretty (SymbMapItems k syms _ _) =
        printSK k <> commaDs syms

-- | print symbol kind
printSK :: SymbKind -> Doc
printSK k =
    case k of Implicit -> empty
              _ -> text (drop 3 $ show k) <> space
