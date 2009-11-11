{- |
Module      :  $Header$
Description :  print the abstract syntax so that it can be re-parsed
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

printing data types of the abstract syntax
-}

module HasCASL.PrintAs where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.FoldTerm
import HasCASL.Builtin

import Common.Id
import Common.Keywords
import Common.DocUtils
import Common.Doc
import Common.AS_Annotation

import qualified Data.Set as Set
import Data.List

-- | short cut for: if b then empty else d
noPrint :: Bool -> Doc -> Doc
noPrint b d = if b then empty else d

noNullPrint :: [a] -> Doc -> Doc
noNullPrint = noPrint . null

semiDs :: Pretty a => [a] -> Doc
semiDs = fsep . punctuate semi . map pretty

semiAnnoted :: Pretty a => [Annoted a] -> Doc
semiAnnoted = vcat . map (printSemiAnno pretty True)

instance Pretty Variance where
    pretty = sidDoc . mkSimpleId . show

instance Pretty a => Pretty (AnyKind a) where
    pretty knd = case knd of
        ClassKind ci ->  pretty ci
        FunKind v k1 k2 _ -> fsep
            [ pretty v <> (case k1 of
                FunKind _ _ _ _ -> parens
                _ -> id) (pretty k1)
            , funArrow, pretty k2]

varOfTypeArg :: TypeArg -> Id
varOfTypeArg (TypeArg i _ _ _ _ _ _) = i

instance Pretty TypePattern where
    pretty tp = case tp of
        TypePattern name@(Id ts cs _) args _ ->
          let ds = map (pretty . varOfTypeArg) args in
            if placeCount name == length args then
                let (ras, dts) = mapAccumL ( \ l t -> if isPlace t then
                          case l of
                            x : r -> (r, x)
                            _ -> error "Pretty TypePattern"
                          else (l, printTypeToken t)) ds ts
                in fsep $ dts ++ (if null cs then [] else
                        [brackets $ sepByCommas $ map printTypeId cs])
                       ++ ras
            else printTypeId name <+> fsep ds
        TypePatternToken t -> printTypeToken t
        MixfixTypePattern ts -> fsep $ map pretty ts
        BracketTypePattern k l _ -> bracket k $ ppWithCommas l
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
printKind k = noPrint (k == universe) $ printVarKind NonVar (VarKind k)

-- | print the kind of a variable with its variance and a preceding colon
printVarKind :: Variance -> VarKind -> Doc
printVarKind e vk = case vk of
    Downset t -> less <+> pretty t
    VarKind k -> colon <+> pretty e <> pretty k
    MissingKind -> empty

data TypePrec = Outfix | Prefix | Lazyfix | ProdInfix | FunInfix | Absfix
    deriving (Eq, Ord)

parenPrec :: TypePrec -> (TypePrec, Doc) -> Doc
parenPrec p1 (p2, d) = if p2 < p1 then d else parens d

printTypeToken :: Token -> Doc
printTypeToken t = let
  l = ("*", cross) : map ( \ (a, d) -> (show a, d) )
    [ (FunArr, funArrow)
    , (PFunArr, pfun)
    , (ContFunArr, cfun)
    , (PContFunArr, pcfun) ]
  in case lookup (tokStr t) l of
       Just d -> d
       _ -> pretty t

printTypeId :: Id -> Doc
printTypeId (Id ts cs _) = let (toks, pls) = splitMixToken ts in
   fcat $ map printTypeToken toks
   ++ (if null cs then [] else [brackets $ sepByCommas $ map printTypeId cs])
   ++ map printTypeToken pls

toMixType :: Type -> (TypePrec, Doc)
toMixType typ = case typ of
    TypeName name _ _ -> (Outfix, printTypeId name)
    TypeToken tt -> (Outfix, printTypeToken tt)
    TypeAbs v t _ ->
        (Absfix, sep [ lambda <+> pretty v, bullet <+> snd (toMixType t)])
    ExpandedType t1 _ -> toMixType t1 -- here we print the unexpanded type
    BracketType k l _ ->
        (Outfix, bracket k $ sepByCommas $ map (snd . toMixType) l)
    KindedType t kind _ -> (Lazyfix, sep
      [ parenPrec Lazyfix $ toMixType t
      , colon <+> printList0 (Set.toList kind)])
    MixfixType ts -> (Prefix, fsep $ map (snd . toMixType) ts)
    TypeAppl t1 t2 -> let
        (topTy, tyArgs) = getTypeApplAux False typ
        aArgs = (Prefix, sep [ parenPrec ProdInfix $ toMixType t1
                             , parenPrec Prefix $ toMixType t2 ])
         in case topTy of
      TypeName name@(Id ts cs _) _k _i ->
        case map toMixType tyArgs of
          [dArg] -> case ts of
               [e] | name == lazyTypeId ->
                   (Lazyfix, pretty e <+> parenPrec Lazyfix dArg)
               [e1, e2, e3] | not (isPlace e1) && isPlace e2
                              && not (isPlace e3) && null cs ->
                   (Outfix, fsep [pretty e1, snd dArg, pretty e3])
               _ -> aArgs
          [dArg1, dArg2] -> case ts of
               [_, e2, _] | isInfix name && null cs ->
                  if tokStr e2 == prodS then
                    (ProdInfix, fsep
                     [ parenPrec ProdInfix dArg1
                     , cross, parenPrec ProdInfix dArg2])
                  else -- assume fun type
                  (FunInfix, fsep
                   [ parenPrec FunInfix dArg1
                   , printTypeToken e2, snd dArg2])
               _ -> aArgs
          dArgs -> if isProductIdWithArgs name $ length tyArgs then
              (ProdInfix, fsep $ punctuate (space <> cross) $
               map (parenPrec ProdInfix) dArgs) else aArgs
      _ -> aArgs

instance Pretty Type where
    pretty = snd . toMixType

printTypeScheme :: PolyId -> TypeScheme -> Doc
printTypeScheme (PolyId _ tys _) (TypeScheme vs t _) =
    let tdoc = pretty t in
    if null vs || not (null tys) then tdoc else
        fsep [forallDoc, semiDs vs, bullet <+> tdoc]

-- no curried notation for bound variables
instance Pretty TypeScheme where
    pretty = printTypeScheme (PolyId applId [] nullRange)

instance Pretty Partiality where
    pretty p = case p of
        Partial -> quMarkD
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
    pretty = printTerm . rmSomeTypes

isSimpleTerm :: Term -> Bool
isSimpleTerm trm = case trm of
    QualVar _ -> True
    QualOp _ _ _ _ _ _ -> True
    ResolvedMixTerm _ _ _ _ -> True
    ApplTerm _ _ _ -> True
    TupleTerm _ _ -> True
    TermToken _ -> True
    BracketTerm _ _ _ -> True
    _ -> False

-- | used only to produce CASL applications
isSimpleArgTerm :: Term -> Bool
isSimpleArgTerm trm = case trm of
    QualVar vd -> not (isPatVarDecl vd)
    QualOp _ _ _ _ _ _ -> True
    ResolvedMixTerm n _ l _ -> placeCount n /= 0 || not (null l)
    TupleTerm _ _ -> True
    BracketTerm _ _ _ -> True
    _ -> False

hasRightQuant :: Term -> Bool
hasRightQuant t = case t of
    QuantifiedTerm {} -> True
    LambdaTerm {} -> True
    CaseTerm {} -> True
    LetTerm Let _ _ _ -> True
    ResolvedMixTerm n _ ts _ | endPlace n && placeCount n == length ts
        -> hasRightQuant (last ts)
    ApplTerm (ResolvedMixTerm n _ [] _) t2 _ | endPlace n ->
        case t2 of
          TupleTerm ts _ | placeCount n == length ts -> hasRightQuant (last ts)
          _ -> hasRightQuant t2
    ApplTerm _ t2 _ -> hasRightQuant t2
    _ -> False

zipArgs :: Id -> [Term] -> [Doc] -> [Doc]
zipArgs n ts ds = case (ts, ds) of
    (t : r, d : s) -> let
        p = parenTermDoc t d
        e = if hasRightQuant t then parens d else p
        in if null r && null s && endPlace n then
               [if hasRightQuant t then d else p]
           else e : zipArgs n r s
    _ -> []

isPatVarDecl :: VarDecl -> Bool
isPatVarDecl (VarDecl v ty _ _) = case ty of
           TypeName t _ _ -> isSimpleId v && isPrefixOf "_v" (show t)
           _ -> False

parenTermDoc :: Term -> Doc -> Doc
parenTermDoc trm = if isSimpleTerm trm then id else parens

printTermRec :: FoldRec Doc (Doc, Doc)
printTermRec = FoldRec
    { foldQualVar = \ _ vd@(VarDecl v _ _ _) ->
         if isPatVarDecl vd then pretty v
         else parens $ keyword varS <+> pretty vd
    , foldQualOp = \ _ br n t tys k _ ->
        (if null tys || k == Infer then id else
          (<> brackets (ppWithCommas tys))) $
          parens $ fsep [pretty br, pretty n, colon, printTypeScheme n $
                         if isPred br then unPredTypeScheme t else t]
    , foldResolvedMixTerm =
        \ (ResolvedMixTerm _ _ os _) n@(Id toks cs ps) tys ts _ ->
          let pn = placeCount n in if pn == length ts || null ts then
            let ds = zipArgs n os ts in
            if null tys then idApplDoc n ds
            else let (ftoks, _) = splitMixToken toks
                     fId = Id ftoks cs ps
                     (fts, rts) = splitAt (placeCount fId) $ if null ts
                          then replicate pn $ pretty placeTok else ds
                 in fsep $ (idApplDoc fId fts <> brackets (ppWithCommas tys))
                    : rts
          else idApplDoc applId [idDoc n, parens $ sepByCommas ts]
    , foldApplTerm = \ (ApplTerm o1 o2 _) t1 t2 _ ->
        case (o1, o2) of
          -- comment out the following two guards for CASL applications
          (ResolvedMixTerm n _ [] _, TupleTerm ts@(_ : _) _)
              | placeCount n == length ts ->
                  idApplDoc n (zipArgs n ts $ map printTerm ts)
          (ResolvedMixTerm n _ [] _, _) | placeCount n == 1
            -> idApplDoc n $ zipArgs n [o2] [t2]
          _ -> idApplDoc applId $ zipArgs applId [o1, o2] [t1, t2]
     , foldTupleTerm = \ _ ts _ -> parens $ sepByCommas ts
     , foldTypedTerm = \ (TypedTerm ot _ _ _) t q typ _ -> fsep [(case ot of
           TypedTerm {} | elem q [Inferred, OfType] -> parens
           ApplTerm (ResolvedMixTerm n _ [] _) arg _ ->
             let pn = placeCount n in case arg of
               TupleTerm ts@(_ : _) _ | pn == length ts -> parens
               _ | pn == 1 || hasRightQuant ot -> parens
               _ -> id
           _ | hasRightQuant ot -> parens
           _ -> id) t, pretty q, pretty typ]
     , foldQuantifiedTerm = \ _ q vs t _ ->
           fsep [pretty q, printGenVarDecls vs, bullet <+> t]
     , foldLambdaTerm = \ (LambdaTerm ops _ _ _) ps q t _ ->
            fsep [ lambda
                 , case ops of
                      [p] -> case p of
                          TupleTerm [] _ -> empty
                          QualVar vd@(VarDecl v ty _ _) ->
                              pretty v <+> if isPatVarDecl vd then empty
                                     else printVarDeclType ty
                          _ -> head ps
                      _ -> if all ( \ p -> case p of
                                QualVar vd -> not $ isPatVarDecl vd
                                _ -> False) ops
                           then printGenVarDecls $ map
                                ( \ (QualVar vd) -> GenVarDecl vd) ops
                           else fcat $ map parens ps
                 , (case q of
                     Partial -> bullet
                     Total -> bullet <> text exMark) <+> t]
     , foldCaseTerm = \ _ t es _  ->
            fsep [text caseS, t, text ofS,
                  cat $ punctuate (space <> bar <> space) $
                       map (printEq0 funArrow) es]
     , foldLetTerm = \ _ br es t _ ->
            let des = sep $ punctuate semi $ map (printEq0 equals) es
                in case br of
                Let -> fsep [sep [text letS <+> des, text inS], t]
                Where -> fsep [sep [t, text whereS], des]
                Program -> text programS <+> des
     , foldTermToken = const pretty
     , foldMixTypeTerm = \ _ q t _ -> pretty q <+> pretty t
     , foldMixfixTerm = const fsep
     , foldBracketTerm = \ _ k l _ -> bracket k $ sepByCommas l
     , foldAsPattern = \ _ (VarDecl v _ _ _) p _ ->
           fsep [pretty v, text asP, p]
     , foldProgEq = \ _ p t _ -> (p, t) }

printTerm :: Term -> Doc
printTerm = foldTerm printTermRec

rmTypeRec :: MapRec
rmTypeRec = mapRec
    { foldQualOp = \ t _ (PolyId i _ _) _ tys k ps ->
        if elem i $ map fst bList then ResolvedMixTerm i
           (if k == Infer then [] else tys) [] ps else t
    , foldTypedTerm = \ _ nt q ty ps -> case q of
        Inferred -> nt
        _ -> case nt of
          TypedTerm tt oq oty _ | oty == ty || oq == InType ->
            if q == AsType then TypedTerm tt q ty ps else nt
          QualVar (VarDecl _ oty _ _) | oty == ty -> nt
          _ -> TypedTerm nt q ty ps }

rmSomeTypes :: Term -> Term
rmSomeTypes = foldTerm rmTypeRec

-- | put parenthesis around applications
parenTermRec :: MapRec
parenTermRec = let
     addParAppl t = case t of
           ResolvedMixTerm _ _ [] _ -> t
           QualVar _ -> t
           QualOp _ _ _ _ _ _ -> t
           TermToken _ -> t
           BracketTerm _ _ _ -> t
           TupleTerm _ _ -> t
           _ -> TupleTerm [t] nullRange
     in mapRec
    { foldApplTerm = \ _ t1 t2 ->
         ApplTerm (addParAppl t1) (addParAppl t2)
    , foldResolvedMixTerm = \ _ n tys ->
        ResolvedMixTerm n tys . map addParAppl
    , foldTypedTerm = \ _ ->
        TypedTerm . addParAppl
    , foldMixfixTerm = \ _ -> MixfixTerm . map addParAppl
    , foldAsPattern = \ _ v -> AsPattern v . addParAppl
    }

parenTerm :: Term -> Term
parenTerm = foldTerm parenTermRec

-- | print an equation with different symbols between pattern and term
printEq0 :: Doc -> (Doc, Doc) -> Doc
printEq0 s (p, t) = sep [p, hsep [s, t]]

printGenVarDecls :: [GenVarDecl] -> Doc
printGenVarDecls = fsep . punctuate semi . map
  ( \ l -> case l of
     [x] -> pretty x
     GenVarDecl (VarDecl _ t _ _) : _ -> sep
       [ ppWithCommas (map ( \ (GenVarDecl (VarDecl v _ _ _)) -> v) l)
       , printVarDeclType t]
     GenTypeVarDecl (TypeArg _ e c _ _ _ _) : _ -> sep
       [ ppWithCommas (map ( \ (GenTypeVarDecl v) -> varOfTypeArg v) l)
       , printVarKind e c]
     _ -> error "printGenVarDecls") . groupBy sameType

sameType :: GenVarDecl -> GenVarDecl -> Bool
sameType g1 g2 = case (g1, g2) of
    (GenVarDecl (VarDecl _ t1 Comma _), GenVarDecl (VarDecl _ t2 _ _))
      | t1 == t2 -> True
    (GenTypeVarDecl (TypeArg _ e1 c1 _ _ Comma _),
     GenTypeVarDecl (TypeArg _ e2 c2 _ _ _ _)) | e1 == e2 && c1 == c2 -> True
    _ -> False

printVarDeclType :: Type -> Doc
printVarDeclType t = case t of
       MixfixType [] -> empty
       _ -> colon <+> pretty t

instance Pretty VarDecl where
    pretty (VarDecl v t _ _) = pretty v <+> printVarDeclType t

instance Pretty GenVarDecl where
    pretty gvd = case gvd of
        GenVarDecl v -> pretty v
        GenTypeVarDecl tv -> pretty tv

instance Pretty TypeArg where
    pretty (TypeArg v e c _ _ _ _) =
        pretty v <+> printVarKind e c

-- | don't print an empty list and put parens around longer lists
printList0 :: (Pretty a) => [a] -> Doc
printList0 l = case l of
    []  -> empty
    [x] -> pretty x
    _   -> parens $ ppWithCommas l

instance Pretty BasicSpec where
    pretty (BasicSpec l) = if null l then specBraces empty else
        changeGlobalAnnos addBuiltins . vcat $ map pretty l

instance Pretty ProgEq where
    pretty (ProgEq p t ps) = printEq0 equals $ foldEq printTermRec
        $ ProgEq (rmSomeTypes p) (rmSomeTypes t) ps

instance Pretty BasicItem where
    pretty bi = case bi of
        SigItems s -> pretty s
        ProgItems l _ -> noNullPrint l $ sep [keyword programS, semiAnnoted l]
        ClassItems i l _ -> noNullPrint l $ let
            b = semiAnnos pretty l
            p = plClass l
            in case i of
            Plain -> topSigKey (classS ++ if p then "es" else "") <+> b
            Instance -> sep [keyword classS <+>
                             keyword (instanceS ++ if p then sS else ""), b]
        GenVarItems l _ -> topSigKey (varS ++ pluralS l) <+> printGenVarDecls l
        FreeDatatype l _ -> sep
            [ keyword freeS <+> keyword (typeS ++ pluralS l)
            , semiAnnos pretty l]
        GenItems l _ -> let gkw = keyword generatedS in
            (if all (isDatatype . item) l then \ i -> gkw <+> rmTopKey i
             else \ i -> sep [gkw, specBraces i])
             $ vcat $ map (printAnnoted pretty) l
        AxiomItems vs fs _ -> sep
            [ if null vs then empty else forallDoc <+> printGenVarDecls vs
           , case fs of
             [] -> empty
             _ -> let pp = addBullet . pretty in
               vcat $ map (printAnnoted pp) (init fs)
                    ++ [printSemiAnno pp True $ last fs]]
        Internal l _ -> sep
            [ keyword internalS
            , specBraces $ vcat $ map (printAnnoted pretty) l]

plClass :: [Annoted ClassItem] -> Bool
plClass l = case map item l of
    _ : _ : _ -> True
    [ClassItem (ClassDecl (_ : _ : _) _ _) _ _] -> True
    _ -> False

pluralS :: [a] -> String
pluralS l = case l of
    _ : _ : _ -> sS
    _ -> ""

isDatatype :: SigItems -> Bool
isDatatype si = case si of
    TypeItems _ l _ -> all
      ((\ t -> case t of
        Datatype _ -> True
        _ -> False) . item) l
    _ -> False

instance Pretty OpBrand where
    pretty = keyword . show

instance Pretty SigItems where
    pretty si = case si of
        TypeItems i l _ -> noNullPrint l $
          let b = semiAnnos pretty l in case i of
            Plain -> topSigKey ((if all (isSimpleTypeItem . item) l
                                then typeS else typeS) ++ plTypes l) <+> b
            Instance ->
              sep [keyword typeS <+> keyword (instanceS ++ plTypes l), b]
        OpItems b l _ -> noNullPrint l $ topSigKey (show b ++ plOps l)
            <+> let po = prettyOpItem $ isPred b in
                if case item $ last l of
                  OpDecl _ _ a@(_ : _) _ -> case last a of
                    UnitOpAttr {} -> True
                    _ -> False
                  OpDefn {} -> True
                  _ -> False
                then vcat (map (printSemiAnno po True) l)
                else semiAnnos po l

plTypes :: [Annoted TypeItem] -> String
plTypes l = case map item l of
    _ : _ : _ -> sS
    [TypeDecl (_ : _ : _) _ _] -> sS
    [SubtypeDecl (_ : _ : _) _ _] -> sS
    [IsoDecl (_ : _ : _) _] -> sS
    _ -> ""

plOps :: [Annoted OpItem] -> String
plOps l = case map item l of
    _ : _ : _ -> sS
    [OpDecl (_ : _ : _) _ _ _] -> sS
    _ -> ""

isSimpleTypeItem :: TypeItem -> Bool
isSimpleTypeItem ti = case ti of
    TypeDecl l k _ -> k == universe && all isSimpleTypePat l
    SubtypeDecl l (TypeName i _ _) _ ->
        not (isMixfix i) && all isSimpleTypePat l
    SubtypeDefn p (Var _) t _ _ ->
        isSimpleTypePat p && isSimpleType t
    _ -> False

isSimpleTypePat :: TypePattern -> Bool
isSimpleTypePat tp = case tp of
    TypePattern i [] _ -> not $ isMixfix i
    _ -> False

isSimpleType :: Type -> Bool
isSimpleType t = case t of
    TypeName i _ _ -> not $ isMixfix i
    TypeToken _ -> True
    MixfixType[TypeToken _, BracketType Squares (_ : _) _] -> True
    _ -> False

instance Pretty ClassItem where
    pretty (ClassItem d l _) = pretty d $+$ noNullPrint l
                   (specBraces $ vcat $ map (printAnnoted pretty) l)

instance Pretty ClassDecl where
    pretty (ClassDecl l k _) = let cs = ppWithCommas l in
        if k == universe then cs else  fsep [cs, less, pretty k]

instance Pretty Vars where
    pretty vd = case vd of
        Var v -> pretty v
        VarTuple vs _ -> parens $ ppWithCommas vs

instance Pretty TypeItem where
    pretty ti = case ti of
        TypeDecl l k _ -> sep [ppWithCommas l, printKind k]
        SubtypeDecl l t _ ->
            fsep [ppWithCommas l, less, pretty t]
        IsoDecl l _ -> fsep $ punctuate (space <> equals) $ map pretty l
        SubtypeDefn p v t f _ ->
            fsep [pretty p, equals,
                  specBraces $ fsep
                  [pretty v, colon <+> pretty t, bullet <+> pretty f]]
        AliasType p _ (TypeScheme l t _) _ ->
            fsep $ pretty p : map (pretty . varOfTypeArg) l
                  ++ [text assignS <+> pretty t]
        Datatype t -> pretty t

printItScheme :: [PolyId] -> Bool -> TypeScheme -> Doc
printItScheme ps b = (case ps of
    [p] -> printTypeScheme p
    _ -> pretty) . (if b then unPredTypeScheme else id)

printHead :: [[VarDecl]] -> [Doc]
printHead = map ((<> space) . parens . printGenVarDecls . map GenVarDecl)

prettyOpItem :: Bool -> OpItem -> Doc
prettyOpItem b oi = case oi of
        OpDecl l t a _ -> fsep $ punctuate comma (map pretty l)
          ++ [colon <+>
              (if null a then id else (<> comma))(printItScheme l b t)]
          ++ punctuate comma (map pretty a)
        OpDefn n ps s t _ -> fcat $
            (if null ps then (<> space) else id) (pretty n)
            : printHead ps
            ++ (if b then [] else [colon <+> printItScheme [n] b s <> space])
            ++ [(if b then equiv else equals) <> space, pretty t]

instance Pretty PolyId where
    pretty (PolyId i@(Id ts cs ps) tys _) = if null tys then pretty i else
      let (fts, plcs) = splitMixToken ts
      in idDoc (Id fts cs ps) <> brackets (ppWithCommas tys)
         <> hcat (map pretty plcs)

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
    pretty (DatatypeDecl p k alts d _) =
        fsep [ pretty p, printKind k, defn
              <+> cat (punctuate (space <> bar <> space)
                      $ map pretty alts)
             , case d of
                 [] -> empty
                 _ -> keyword derivingS <+> ppWithCommas d]

instance Pretty Alternative where
    pretty alt = case alt of
        Constructor n cs p _ -> pretty n <+> fsep
          (map ( \ l -> case (l, p) of
-- comment out the following line to output real CASL
            ([NoSelector (TypeToken t)], Total) | isSimpleId n -> pretty t
            _ -> parens $ semiDs l) cs) <> pretty p
        Subtype l _ -> text (if all isSimpleType l then typeS else typeS)
            <+> ppWithCommas l

instance Pretty Component where
    pretty sel = case sel of
        Selector n _ t _ _ -> sep [pretty n, colon <+> pretty t]
        NoSelector t -> pretty t

instance Pretty Symb where
    pretty (Symb i mt _) =
        sep $ pretty i : case mt of
            Nothing -> []
            Just (SymbType t) -> [colon <+> pretty t]

instance Pretty SymbItems where
    pretty (SymbItems k syms _ _) =
        printSK k syms <> ppWithCommas syms

instance Pretty SymbOrMap where
    pretty (SymbOrMap s mt _) =
        sep $ pretty s : case mt of
            Nothing -> []
            Just t -> [mapsto <+> pretty t]

instance Pretty SymbMapItems where
    pretty (SymbMapItems k syms _ _) =
        printSK k syms <> ppWithCommas syms

-- | print symbol kind
printSK :: SymbKind -> [a] -> Doc
printSK k l = case k of
      Implicit -> empty
      _ -> keyword (drop 3 (show k) ++ case l of
        _ : _ : _ -> sS
        _ -> "") <> space
