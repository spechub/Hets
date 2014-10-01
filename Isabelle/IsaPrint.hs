{- |
Module      :  $Header$
Description :  printing Isabelle entities
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Printing functions for Isabelle logic.
-}

module Isabelle.IsaPrint
    ( showBaseSig
    , printIsaTheory
    , getAxioms
    , printNamedSen
    , printTerm
    ) where

import Isabelle.IsaSign
import Isabelle.IsaConsts
import Isabelle.Translate

import Common.AS_Annotation
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Doc hiding (bar)
import Common.DocUtils
import Common.Utils (number)

import Data.Char
import Data.List
import Data.Maybe (isNothing, catMaybes)

printIsaTheory :: String -> Sign -> [Named Sentence] -> Doc
printIsaTheory tn sign sens = let
    b = baseSig sign
    bs = showBaseSig b
    ld = "$HETS_ISABELLE_LIB/"
    mlFileUse = text mlFileS <+> doubleQuotes (text $ ld ++ "prelude.ML")
    in text theoryS <+> text tn
    $+$ text importsS <+> fsep (case b of
        Custom_thy -> []
        _ -> if case b of
                Main_thy -> False
                HOLCF_thy -> False
                Custom_thy -> True
                _ -> True then [doubleQuotes $ text $ ld ++ bs] else [text bs]
      ++ map (doubleQuotes . text) (imports sign))
    $+$ text beginS
    $++$ mlFileUse
    $++$ printTheoryBody sign sens
    $++$ text endS

printTheoryBody :: Sign -> [Named Sentence] -> Doc
printTheoryBody sig sens =
 let (sens', recFuns) = findTypesForRecFuns sens (constTab sig)
     sig' = sig { constTab =
      Map.filterWithKey (\ k _ -> notElem (new k) recFuns) (constTab sig) }
 in callSetup "initialize" (brackets $ sepByCommas
      $ map (text . show . Quote . senAttr)
      $ filter (\ s -> not (isConstDef s || isRecDef s || isInstance s)
                && senAttr s /= "") sens')
      $++$ printSign sig'
      $++$ printNamedSentences sens'
      $++$ printMonSign sig'

findTypesForRecFuns :: [Named Sentence] -> ConstTab
 -> ([Named Sentence], [String])
findTypesForRecFuns ns ctab =
 let (sens, recFuns') = unzip $ map (\ sen ->
      let (sen', recFns') =
           case sentence sen of
             RecDef kw cName cType tm ->
              (case Map.toList $
                 Map.filterWithKey (\ k _ -> new k == new cName) ctab of
                 (_, t) : _ ->
                  case cType of
                   Nothing ->
                    RecDef kw cName (Just t) tm
                   Just t' ->
                    if t /= t' then error "recFun: two types given"
                    else sentence sen
                 [] -> sentence sen
              , Just cName)
             _ -> (sentence sen, Nothing)
      in (sen {sentence = sen'}, recFns')) ns
 in (sens, map new $ catMaybes recFuns')

printNamedSentences :: [Named Sentence] -> Doc
printNamedSentences sens = case sens of
  [] -> empty
  s : r
    | isIsaAxiom s ->
      let (axs, rest) = span isAxiom sens in
      (if null axs then empty else text axiomatizationS $+$ text whereS)
      $+$ vcat (intersperse (text andS) $ map printNamedSen axs)
      $++$ vcat (map ( \ a -> text declareS <+> text (senAttr a)
                        <+> brackets (text simpS))
                 $ filter ( \ a -> case sentence a of
                       b@Sentence {} -> isSimp b && senAttr a /= ""
                       _ -> False) axs)
      $++$ printNamedSentences rest
    | isConstDef s ->
      let (defs_, rest) = span isConstDef sens in
      text defsS $+$ vsep (map printNamedSen defs_)
      $++$ printNamedSentences rest
    | otherwise ->
      printNamedSen s $++$ (case senAttr s of
        n | n == "" || isRecDef s -> empty
          | otherwise -> callSetup "record" (text $ show $ Quote n))
      $++$ printNamedSentences r

callSetup :: String -> Doc -> Doc
callSetup fun args =
    text "setup" <+> doubleQuotes (fsep [text ("Header." ++ fun), args])

data QuotedString = Quote String
instance Show QuotedString where
    show (Quote s) = init . tail . show $ show s

getAxioms :: [Named Sentence] -> ([Named Sentence], [Named Sentence])
getAxioms = partition isIsaAxiom

isIsaAxiom :: Named Sentence -> Bool
isIsaAxiom s = case sentence s of
  Sentence {} -> isAxiom s
  _ -> False

isInstance :: Named Sentence -> Bool
isInstance s = case sentence s of
  Instance {} -> True
  _ -> False

isConstDef :: Named Sentence -> Bool
isConstDef s = case sentence s of
  ConstDef {} -> True
  _ -> False

isRecDef :: Named Sentence -> Bool
isRecDef s = case sentence s of
  RecDef {} -> True
  _ -> False

-- --------------------- Printing functions -----------------------------

showBaseSig :: BaseSig -> String
showBaseSig = takeWhile (/= '_') . show

printClass :: IsaClass -> Doc
printClass (IsaClass x) = text x

printSort :: Sort -> Doc
printSort = printSortAux False

printSortAux :: Bool -> Sort -> Doc
printSortAux b l = case l of
    [c] -> printClass c
    _ -> (if b then doubleQuotes else id)
      . braces . hcat . punctuate comma $ map printClass l

data SynFlag = Quoted | Unquoted | Null

doubleColon :: Doc
doubleColon = text "::"

isaEquals :: Doc
isaEquals = text "=="

bar :: [Doc] -> [Doc]
bar = punctuate $ space <> text "|"

printType :: Typ -> Doc
printType = printTyp Unquoted

printTyp :: SynFlag -> Typ -> Doc
printTyp a = fst . printTypeAux a

printTypeAux :: SynFlag -> Typ -> (Doc, Int)
printTypeAux a t = case t of
 TFree v s -> (let
        d = text $ if isPrefixOf "\'" v || isPrefixOf "?\'" v
                                then v else '\'' : v
        c = printSort s
     in if null s then d else case a of
         Quoted -> d <> doubleColon <> if null
                     $ tail s then c else doubleQuotes c
         Unquoted -> d <> doubleColon <> c
         Null -> d, 1000)
 TVar iv s -> printTypeAux a $ TFree (unindexed iv) s
 Type name _ args -> case args of
    [t1, t2] | elem name [prodS, sProdS, funS, cFunS, lFunS, sSumS] ->
       printTypeOp a name t1 t2
    _ -> ((case args of
           [] -> empty
           [arg] -> let (d, i) = printTypeAux a arg in
                      if i < 1000 then parens d else d
           _ -> parens $ hsep $ punctuate comma $
                       map (fst . printTypeAux a) args)
          <+> text name, 1000)

printTypeOp :: SynFlag -> TName -> Typ -> Typ -> (Doc, Int)
printTypeOp x name r1 r2 =
    let (d1, i1) = printTypeAux x r1
        (d2, i2) = printTypeAux x r2
        (l, r) = Map.findWithDefault (0 :: Int, 0 :: Int)
                    name $ Map.fromList
                    [ (funS, (1, 0))
                    , (cFunS, (1, 0))
                    , (lFunS, (1, 0))
                    , (sSumS, (11, 10))
                    , (prodS, (21, 20))
                    , (sProdS, (21, 20))
                    , (lProdS, (21, 20))
                    ]
        d3 = if i1 < l then parens d1 else d1
        d4 = if i2 < r then parens d2 else d2
    in (d3 <+> text name <+> d4, r)

andDocs :: [Doc] -> Doc
andDocs = vcat . prepPunctuate (text andS <> space)

-- | printing a named sentence
printNamedSen :: Named Sentence -> Doc
printNamedSen ns =
  let s = sentence ns
      lab = senAttr ns
      b = isAxiom ns
      d = printSentence s
  in case s of
  TypeDef {} -> d
  RecDef {} -> d
  Lemmas {} -> d
  Instance {} -> d
  Locale {} -> d
  Class {} -> d
  Datatypes _ -> d
  Consts _ -> d
  TypeSynonym {} -> d
  Axioms _ -> d
  Lemma {} -> d
  Definition {} -> d
  Fun {} -> d
  Instantiation {} -> d
  InstanceProof {} -> d
  InstanceArity {} -> d
  InstanceSubclass {} -> d
  Subclass {} -> d
  Typedef {} -> d
  Defs {} -> d
  Fixrec {} -> d
  Domains {} -> d
  Primrec {} -> d
  _ -> let dd = doubleQuotes d in
       if isRefute s then text lemmaS <+> text lab <+> colon
              <+> dd $+$ text refuteS
       else if null lab then dd else fsep [ (case s of
    ConstDef {} -> text $ lab ++ "_def"
    Sentence {} ->
        (if b then empty else text theoremS)
        <+> text lab <+> (if b then text "[rule_format]" else
            if isSimp s then text "[simp]" else empty)
    _ -> error "printNamedSen") <+> colon, dd] $+$ case s of
    Sentence {} -> if b then empty else case thmProof s of
      Nothing -> text oopsS
      Just prf -> pretty prf
    _ -> empty

-- | sentence printing
printSentence :: Sentence -> Doc
printSentence s = case s of
  TypeDef nt td pr -> text typedefS
                   <+> printType nt
                   <+> equals
                   <+> doubleQuotes (printSetDecl td)
                   $+$ pretty pr
  RecDef kw cName cType xs ->
    let preparedEq = map (doubleQuotes . printTerm) xs
        preparedEqWithBars =
          map (<+> text barS) (init preparedEq) ++ [last preparedEq]
        tp = case cType of
              Just t -> doubleColon <+> doubleQuotes (printType t)
              Nothing -> empty
        kw' = case kw of
               Just str -> text str
               Nothing -> text primrecS
    in kw' <+> text (new cName) <+> tp <+> printAlt cName <+> text whereS $+$
       vcat preparedEqWithBars
  Instance { tName = t, arityArgs = args, arityRes = res, definitions = defs_,
             instProof = prf } ->
      text instantiationS <+> text t <> doubleColon <> (case args of
        [] -> empty
        _ -> parens $ hsep $ punctuate comma $ map (printSortAux True) args)
        <+> printSortAux True res $+$ text beginS $++$ printDefs defs_ $++$
            text instanceS <+> pretty prf $+$ text endS
      where printDefs :: [(String, Term)] -> Doc
            printDefs defs' = vcat (map printDef defs')
            printDef :: (String, Term) -> Doc
            printDef (name, def) =
                text definitionS <+>
                     printNamedSen (makeNamed name (ConstDef def))

  Sentence { isRefuteAux = b, metaTerm = t } -> printPlainMetaTerm (not b) t
  ConstDef t -> printTerm t
  Lemmas name lemmas -> if null lemmas
                        then empty {- only have this lemmas if we have some in
                                   the list -}
                        else text lemmasS <+> text name <+>
                             equals <+> sep (map text lemmas)
  l@(Locale {}) ->
   let h = text "locale" <+> text (show $ localeName l)
       parents = Data.List.intersperse (text "+") $
                  map (text . show) (localeParents l)
       (fxs, ass) = printContext $ localeContext l
   in printFixesAssumes h parents ass fxs
      $+$ printBody (localeBody l)
  c@(Class {}) ->
   let h = text "class" <+> text (show $ className c)
       parents = Data.List.intersperse (text "+") $
                  map (text . show) (classParents c)
       (fxs, ass) = printContext (classContext c)
   in printFixesAssumes h parents ass fxs
      $+$ printBody (classBody c)
  (Datatypes dts) -> if null dts then empty
                     else text "datatype" <+>
                        andDocs (map (\ d ->
                        let vars = map printType $ datatypeTVars d
                            name = text $ show $ datatypeName d
                            pretty_cs c =
                             let cname = case c of
                                  DatatypeNoConstructor {} -> ""
                                  _ -> show $ constructorName c
                                 cname' = if any isSpace cname
                                          then doubleQuotes (text cname)
                                          else text cname
                                 tps = map (doubleQuotes . printType) $
                                         constructorArgs c
                             in hsep (cname' : tps)
                            cs = map pretty_cs $ datatypeConstructors d
                        in hsep vars <+> name <+> text "=" <+>
                           fsep (bar cs)) dts)
  Domains ds -> if null ds then empty
                else text "domain" <+>
                 andDocs (map (\ d ->
                  let vars = map printType $ domainTVars d
                      name = text $ show $ domainName d
                      pretty_cs c =
                       let cname = text $ show $ domainConstructorName c
                           args' = map (\ arg ->
                            (if domainConstructorArgLazy arg
                             then text "lazy" else empty) <+>
                            (case domainConstructorArgSel arg of
                              Just sel -> text (show sel) <+> text "::"
                              Nothing -> empty) <+> (doubleQuotes . printType)
                            (domainConstructorArgType arg)) $
                            domainConstructorArgs c
                           args = map parens args'
                       in hsep $ cname : args
                      cs = map pretty_cs $ domainConstructors d
                  in hsep vars <+> name <+> text "=" <+>
                     fsep (bar cs)) ds)
  Consts cs -> if null cs then empty
               else vsep $ text "consts" :
                     map (\ (n, _, t) -> text n <+> text "::" <+>
                                    doubleQuotes (printType t)) cs
  TypeSynonym n _ vs tp -> hsep $ [text "type_synonym",
                                 text $ show n, text "="] ++ map text vs
                                ++ [doubleQuotes . printType $ tp]
  Axioms axs -> if null axs then empty
                else vsep $ text "axioms" :
                      map (\ a -> text (show $ axiomName a) <+>
                                 (if axiomArgs a /= ""
                                  then brackets (text $ axiomArgs a)
                                  else empty) <+> text ":" <+>
                                 doubleQuotes (printTerm $ axiomTerm a)) axs
  l@(Lemma {}) ->
   let (fxs, ass) = printContext $ lemmaContext l
   in text "lemma" <+> (case lemmaTarget l of
                           Just t -> braces (text "in" <+> text (show t))
                           Nothing -> empty) <+>
                           (case (null fxs, null ass, lemmaProps l) of
                            (True, True, [sh]) -> printProps sh
                            _ -> vsep (fxs ++ ass ++
                                  [text "shows" <+> andDocs
                                    (map printProps (lemmaProps l))]))
      $+$ (case lemmaProof l of
            Just p -> text p
            Nothing -> empty)
  d@(Definition {}) -> fsep [text "definition" <+>
   (case definitionTarget d of
     Just t -> braces (text "in" <+> text (show t))
     Nothing -> empty) <+>
   (text (show $ definitionName d) <+> text "::" <+>
    doubleQuotes (printType $ definitionType d)), text "where" <+>
   doubleQuotes (text (show $ definitionName d) <+> hsep (map printTerm (
    definitionVars d)) <+> text "=" <+> printTerm (definitionTerm d))]
  f@(Fun {}) -> text "fun" <+> (case funTarget f of
   Just t -> braces (text "in" <+> text (show t))
   Nothing -> empty) <+> (if funDomintros f then braces (text "domintros")
    else empty) <+> vcat (intersperse (text andS) $
     map (\ (name, mx, tp, _) -> text name <+> text "::" <+>
     doubleQuotes (printType tp) <+> case mx of
                      Just (Mixfix _ _ s' _) -> doubleQuotes (text s')
                      _ -> empty) (funEquations f)) <+> text "where" $+$
    (let eqs = concatMap (\ (name, _, _, e) -> map (\ e' -> (name, e')) e)
                             (funEquations f)
         eqs' = map (\ (n, (vs, t)) -> doubleQuotes (text n <+>
                 hsep (map printTerm vs) <+>
                 text "=" <+> printTerm t)) eqs
     in fsep $ bar eqs')
  i@(Instantiation {}) -> fsep $ (text "instantiation" <+> text
   (instantiationType i) <+> text "::" <+> printArity (instantiationArity i)) :
    [printBody (instantiationBody i)]
  InstanceProof prf -> text "instance" $+$ text prf
  i@(InstanceArity {}) -> text "instance" <+>
   hcat (intersperse (text "and") $ map text $ instanceTypes i) <+>
   printArity (instanceArity i) $+$ text (instanceProof i)
  i@(InstanceSubclass {}) -> text "instance" <+> text (instanceClass i) <+>
   text (instanceRel i) <+> text (instanceClass1 i) $+$ text (instanceProof i)
  c@(Subclass {}) -> text "subclass" <+> (case subclassTarget c of
                           Just t -> braces (text "in" <+> text (show t))
                           Nothing -> empty) <+> text (subclassClass c)
                          <+> text (subclassProof c)
  t@(Typedef {}) -> text "typedef" <+> (case typedefVars t of
                     [] -> empty
                     [v] -> printVarWithSort v
                     vs -> parens $ hsep $ punctuate comma $
                           map printVarWithSort vs) <+>
                    text (show $ typedefName t) <+> text "=" <+>
                    doubleQuotes (printTerm $ typedefTerm t) <+>
                    (case typedefMorphisms t of
                      Just (m1, m2) -> text "morphisms" <+> text (show m1)
                                     <+> text (show m2)
                      Nothing -> empty) $+$ text (typedefProof t)
  d@(Defs {}) -> fsep $ (text "defs" <+> (if defsUnchecked d
                                          then text "unchecked"
                                          else empty) <+>
                                         (if defsOverloaded d
                                          then text "overloaded"
                                          else empty))
   : map (\ eq' ->
       text (show (defEquationName eq')) <+> text ":" <+> doubleQuotes (
        text (defEquationConst eq') <+> text "==" <+>
        printTerm (defEquationTerm eq')) <+> if null (defEquationArgs eq')
        then empty else brackets (text $ defEquationArgs eq')) (defsEquations d)
  Fixrec fs ->
   let h = map (\ (name, _, tp, _) -> text name <+> text "::" <+>
                                  (doubleQuotes . printType) tp) fs
       pretty_fixreceq name eq' =
        let unchecked = if fixrecEquationUnchecked eq' then
                        text "(unchecked)" else empty
            premises = fixrecEquationPremises eq'
            p s' = punctuate $ space <> text s'
            patterns = map (parens . printTerm) $ fixrecEquationPatterns eq'
            tm = printTerm $ fixrecEquationTerm eq'
        in unchecked <+> doubleQuotes (printTermWithPremises premises
            (hsep (p "\\<cdot>" (text name : patterns)) <+> text "=" <+> tm))
       body = concatMap (\ (name, _, _, eqs) -> map (pretty_fixreceq name) eqs)
               fs
   in text "fixrec" <+> andDocs h <+> text "where" $+$ fsep (bar body)
  Primrec t eqs ->
                let h = map (\ (name, _, tp, _) -> text name <+> text "::" <+>
                              (doubleQuotes . printType) tp) eqs
                    pretty_primrec name (vs, tm) = doubleQuotes (text name
                     <+> hsep (map printTerm vs) <+> text "=" <+> printTerm tm)
                    body = concatMap (\ (name, _, _, tms) ->
                            map (pretty_primrec name) tms) eqs
                in text "primrec" <+> (case t of
                           Just t' -> braces (text "in" <+> text (show t'))
                           Nothing -> empty) <+> andDocs h <+> text "where"
                   $+$ fsep (bar body)

printTermWithPremises :: [Term] -> Doc -> Doc
printTermWithPremises ps t =
 let p s = punctuate $ space <> text s
 in fsep $ p "\\<Longrightarrow>" (map printTerm ps ++ [t])

printArity :: (Sort, [Sort]) -> Doc
printArity (sort', sorts) = parens (hsep $ punctuate comma $
                           map (printSortAux True) sorts) <+> printSort sort'

printVarWithSort :: (String, Sort) -> Doc
printVarWithSort (name, []) = text name
printVarWithSort (name, sort') = text name <+> printSortAux True sort'

printBody :: [Sentence] -> Doc
printBody sens = fsep $ if null sens then []
               else [text "begin"] ++ map printSentence sens ++ [text "end"]

printContext :: Ctxt -> ([Doc], [Doc])
printContext ctxt =
 let fixes' = map (\ (n, _, tp) -> if n == "" then empty else text n
                       <+> text "::" <+> (doubleQuotes . printTyp Null) tp)
                     (fixes ctxt)
     assumes' = map (\ (n, tm) -> if n == "" then empty else text n <+> text ":"
                       <+> (doubleQuotes . printTerm) tm)
                     (assumes ctxt)
 in (fixes', assumes')

printProps :: Props -> Doc
printProps (Props {propsName = n, propsArgs = a, props = p}) =
 printMaybe (text . show) n <+> printMaybe text a
 <+> (if isNothing n && isNothing a
      then empty else text ":") <+>
     vcat (map printProp p)

printProp :: Prop -> Doc
printProp (Prop {prop = t, propPats = ts}) =
 let t' = doubleQuotes $ printTerm t
     ts' = hsep $ map (\ p -> text "is" <+> (doubleQuotes . printTerm) p) ts
 in t' <+> if null ts then empty
           else parens ts'

printSetDecl :: SetDecl -> Doc
printSetDecl setdecl =
    case setdecl of
      SubSet v t f -> braces $ printTerm v <> doubleColon <> printType t <> dot
                      <+> printTerm f
      FixedSet elems -> braces $ sepByCommas $ map printTerm elems

printPlainMetaTerm :: Bool -> MetaTerm -> Doc
printPlainMetaTerm b mt = case mt of
    Term t -> printPlainTerm b t
    Conditional conds t -> sep
      [ text premiseOpenS
        <+> fsep (punctuate semi $ map printTerm conds)
        <+> text premiseCloseS
      , text metaImplS <+> printTerm t ]

-- | print plain term
printTerm :: Term -> Doc
printTerm = printPlainTerm True

printPlainTerm :: Bool -> Term -> Doc
printPlainTerm b = fst . printTrm b

-- | print parens but leave a space if doc starts or ends with a bar
parensForTerm :: Doc -> Doc
parensForTerm d =
    let s = show d
        b = '|'
    in parens $ if null s then d
                else (if head s == b then (space <>) else id)
                         ((if last s == b then (<> space) else id) d)

printParenTerm :: Bool -> Int -> Term -> Doc
printParenTerm b i t = case printTrm b t of
    (d, j) -> if j < i then parensForTerm d else d

flatTuplex :: [Term] -> Continuity -> [Term]
flatTuplex cs c = case cs of
    [] -> cs
    _ -> case last cs of
           Tuplex rs@(_ : _ : _) d | d == c -> init cs ++ flatTuplex rs d
           _ -> cs

printMixfixAppl :: Bool -> Continuity -> Term -> [Term] -> (Doc, Int)
printMixfixAppl b c f args = case f of
        Const (VName n (Just (AltSyntax s is i))) (Hide {}) ->
             if length is == length args &&
                (b || n == cNot || isPrefixOf "op " n) then
                   (fsep $ replaceUnderlines s
                     $ zipWith (printParenTerm b) is args, i)
             else printApp b c f args
        Const vn _ | new vn `elem` [allS, exS, ex1S] -> case args of
            [Abs v t _] -> (fsep [text (new vn) <+> printPlainTerm False v
                    <> dot
                    , printPlainTerm b t], lowPrio)
            _ -> printApp b c f args
        App g a d | c == d -> printMixfixAppl b c g (a : args)
        _ -> printApp b c f args

-- | print the term using the alternative syntax (if True)
printTrm :: Bool -> Term -> (Doc, Int)
printTrm b trm = case trm of
    Const vn ty -> let
        dvn = text $ new vn
        nvn = case ty of
            Hide {} -> dvn
            Disp w _ _ -> parens $ dvn <+> doubleColon <+> printType w
      in case altSyn vn of
          Nothing -> (nvn, maxPrio)
          Just (AltSyntax s is i) -> if b && null is then
              (fsep $ replaceUnderlines s [], i) else (nvn, maxPrio)
    Free vn -> (text $ new vn, maxPrio)
    Abs v t c -> (text (case c of
        NotCont -> "%"
        IsCont _ -> "Lam") <+> printPlainTerm False v <> dot
                    <+> printPlainTerm b t, lowPrio)
    If i t e c -> let d = fsep [printPlainTerm b i,
                        text (case c of
                                 NotCont -> "then"
                                 IsCont _ -> "THEN")
                            <+> printPlainTerm b t,
                        text (case c of
                                 NotCont -> "else"
                                 IsCont _ -> "ELSE")
                            <+> printPlainTerm b e]
                  in case c of
        NotCont -> (text "if" <+> d, lowPrio)
        IsCont _ -> (text "IF" <+> d <+> text "FI", maxPrio)
    Case e ps -> (text "case" <+> printPlainTerm b e <+> text "of"
        $+$ vcat (bar $ map (\ (p, t) ->
               fsep [ printPlainTerm b p <+> text "=>"
                    , printParenTerm b (lowPrio + 1) t]) ps), lowPrio)
    Let es i -> (fsep [text "let" <+>
           vcat (punctuate semi $
               map (\ (p, t) -> fsep [ printPlainTerm b p <+> equals
                                       , printPlainTerm b t]) es)
           , text "in" <+> printPlainTerm b i], lowPrio)
    IsaEq t1 t2 ->
        (fsep [ printParenTerm b (isaEqPrio + 1) t1 <+> isaEquals
                         , printParenTerm b isaEqPrio t2], isaEqPrio)
    Tuplex cs c -> case c of
        NotCont -> (parensForTerm
                      $ sepByCommas (map (printPlainTerm b)
                          $ flatTuplex cs c)
                    , maxPrio)
        IsCont _ -> case cs of
                        [] -> error "IsaPrint, printTrm"
                        [a] -> printTrm b a
                        a : aa -> printTrm b $ App (App
                                  lpairTerm a $ IsCont False)
                                     (Tuplex aa c) (IsCont False)
    App f a c -> printMixfixAppl b c f [a]
    Set setdecl -> (printSetDecl setdecl, lowPrio)

printApp :: Bool -> Continuity -> Term -> [Term] -> (Doc, Int)
printApp b c t l = case l of
     [] -> printTrm b t
     _ -> printDocApp b c (printParenTerm b (maxPrio - 1) t) l

printDocApp :: Bool -> Continuity -> Doc -> [Term] -> (Doc, Int)
printDocApp b c d l =
    ( fsep $ (case c of
        NotCont -> id
        IsCont True -> punctuate $ text " $$"
        IsCont False -> punctuate $ text " $")
          $ d : map (printParenTerm b maxPrio) l
    , maxPrio - 1)

replaceUnderlines :: String -> [Doc] -> [Doc]
replaceUnderlines str l = case str of
    "" -> []
    '\'' : r@(q : s) -> if q `elem` "_/'()"
                       then consDocBarSep (text [q]) $ replaceUnderlines s l
                       else consDocBarSep (text "'") $ replaceUnderlines r l
    '_' : r -> case l of
                  h : t -> consDocBarSep h $ replaceUnderlines r t
                  _ -> error "replaceUnderlines"
    '/' : ' ' : r -> empty : replaceUnderlines r l
    q : r -> if q `elem` "()/" then replaceUnderlines r l
             else consDocBarSep (text [q]) $ replaceUnderlines r l

consDocBarSep :: Doc -> [Doc] -> [Doc]
consDocBarSep d r = case r of
  [] -> [d]
  h : t -> let
    b = '|'
    hs = show h
    ds = show d
    hhs = head hs
    lds = last ds
    in if null hs || null ds then (d <> h) : t else
           if hhs == b && lds == '(' || last ds == b && hhs == ')'
           then (d <+> h) : t
           else (d <> h) : t

-- end of term printing

printLocales :: Locales -> Doc
printLocales = vsep . map printLocale . orderLDecs . Map.toList

printDefinitions :: Defs -> Doc
printDefinitions = vsep . map printDefinition . Map.toList

printFunctions :: Funs -> Doc
printFunctions = vsep . map printFunction . Map.toList

printFixesAssumes :: Doc -> [Doc] -> [Doc] -> [Doc] -> Doc
printFixesAssumes h p' a f = vcat
  [ h <+> (if null $ p' ++ a ++ f then empty else text "=") <+> hsep p'
    <+> if null p' || null a && null f then empty else text "+"
  , if null f then empty else text "fixes" <+> andDocs f
  , if null a then empty else text "assumes" <+> andDocs a
  ]

printDefinition :: (String, Def) -> Doc
printDefinition (n, (tp, vs, tm)) = text "definition" <+> text n <+> text "::"
 $+$ (doubleQuotes . printTyp Null) tp <+> text "where"
 $+$ doubleQuotes (text n <+> hsep (map (text . fst) vs)
 <+> text "\\<equiv>" <+> printTerm tm)

printFunction :: (String, FunDef) -> Doc
printFunction (n, (tp, def_eqs)) = text "fun" <+> text n <+> text "::"
 $+$ (doubleQuotes . printTyp Null) tp <+> text "where"
 $+$ (vcat . punctuate (text "|"))
      (map (\ (pats, tm) -> doubleQuotes $ text n
       <+> hsep (map printTerm pats) <+> text "="
       <+> printTerm tm) def_eqs)

printLocale :: (String, LocaleDecl) -> Doc
printLocale (n, (parents, in_ax, ex_ax, params)) =
 let p' = Data.List.intersperse (text "+") $ map text parents
     a = map (\ (s, t) -> text s <+> text ":"
           <+> (doubleQuotes . printTerm) t) in_ax
     f = map (\ (s, t, alt) -> text s <+> text "::"
                 <+> (doubleQuotes . printTyp Null) t
                 <+> (case alt of
                       Just (AltSyntax s' [i1, i2] i) -> parens (
                        text (if i1 == i2 then "infix "
                        else if i1 < i2 then "infixr "
                        else "infixl ") <+> doubleQuotes (text s')
                        <+> text (show i))
                       _ -> empty
                 )) params
 in vcat [
     printFixesAssumes (text "locale" <+> text n) p' a f,
     vcat (map (\ (s, t) -> text ("theorem (in " ++ n ++ ")")
           <+> text s <+> text ":"
           <+> (doubleQuotes . printTerm) t
           <+> text "apply(auto)"
           <+> text "done") ex_ax)]

printClassrel :: Classrel -> Doc
printClassrel = vsep . map printClassR . orderCDecs . Map.toList

printClassR :: (IsaClass, ClassDecl) -> Doc
printClassR (y, (parents, assumptions, fxs)) =
 let a = map (\ (s, t) -> text s <+> text ":"
          <+> (doubleQuotes . printTerm) t) assumptions
     f = map (\ (s, t) -> text s <+> text "::"
          <+> (doubleQuotes . printTyp Null) t) fxs
     parents' = filter (\ (IsaClass s) -> notElem s
       ["HOL.type_class", "HOL.type", "type", "type_class"]) parents
     p' = Data.List.intersperse (text "+") $ map printClass parents'
 in printFixesAssumes (text "class" <+> printClass y) p' a f

orderCDecs :: [(IsaClass, ClassDecl)] -> [(IsaClass, ClassDecl)]
orderCDecs =
   topSort crord
 where
   crord (_, (cs, _, _)) (c, _) = elem c cs

orderLDecs :: [(String, LocaleDecl)] -> [(String, LocaleDecl)]
orderLDecs =
   topSort crord
 where
   crord (_, (cs, _, _, _)) (c, _) = elem c cs

printMonArities :: String -> Arities -> Doc
printMonArities tn = vcat . map ( \ (t, cl) ->
                  vcat $ map (printThMorp tn t) cl) . Map.toList

printThMorp :: String -> TName -> (IsaClass, [(Typ, Sort)]) -> Doc
printThMorp tn t xs = case xs of
   (IsaClass "Monad", _) ->
      if isSuffixOf "_mh" tn || isSuffixOf "_mhc" tn
      then printMInstance tn t
      else error "IsaPrint, printInstance: monads not supported"
   _ -> empty

printMInstance :: String -> TName -> Doc
printMInstance tn t = let nM = text (t ++ "_tm")
                          nM2 = text (t ++ "_tm2")
 in prnThymorph nM "MonadType" tn t [("MonadType.M", "'a")] []
    $+$ text "t_instantiate MonadOps mapping" <+> nM
    $+$ text "renames:" <+>
       brackMapList (\ x -> t ++ "_" ++ x)
            [("MonadOpEta.eta", "eta"), ("MonadOpBind.bind", "bind")]
    $+$ text "without_syntax"
    $++$ text "defs "
    $+$ text (t ++ "_eta_def:") <+> doubleQuotes
          (text (t ++ "_eta") <+> isaEquals <+> text ("return_" ++ t))
    $+$ text (t ++ "_bind_def:") <+> doubleQuotes
          (text (t ++ "_bind") <+> isaEquals <+> text ("mbind_" ++ t))
    $++$ lunitLemma t
    $+$ runitLemma t
    $+$ assocLemma t
    $+$ etaInjLemma t
    $++$ prnThymorph nM2 "MonadAxms" tn t [("MonadType.M", "'a")]
        [("MonadOpEta.eta", t ++ "_eta"),
         ("MonadOpBind.bind", t ++ "_bind")]
    $+$ text "t_instantiate Monad mapping" <+> nM2
    $+$ text "renames:" <+>
       brackMapList (\ x -> t ++ "_" ++ x)
           [("Monad.kapp", "kapp"),
            ("Monad.lift", "lift"),
            ("Monad.lift", "lift"),
            ("Monad.mapF", "mapF"),
            ("Monad.bind'", "mbbind"),
            ("Monad.joinM", "joinM"),
            ("Monad.kapp2", "kapp2"),
            ("Monad.kapp3", "kapp3"),
            ("Monad.lift2", "lift2"),
            ("Monad.lift3", "lift3")]
    $+$ text "without_syntax"
    $++$ text " "
 where
  lunitLemma w = text lemmaS <+> text (w ++ "_lunit:")
        <+> doubleQuotes (text (w ++ "_bind")
        <+> parens (text (w ++ "_eta x"))
        <+> parens (text $ "t::'a => 'b " ++ w)
        <+> equals <+> text "t x")
    $+$ text "sorry "
  runitLemma w = text lemmaS <+> text (w ++ "_runit:")
        <+> doubleQuotes (text (w ++ "_bind")
        <+> parens (text $ "t::'a " ++ w) <+> text (w ++ "_eta")
        <+> equals <+> text "t")
    $+$ text "sorry "
  assocLemma w = text lemmaS <+> text (w ++ "_assoc:")
        <+> doubleQuotes (text (w ++ "_bind")
        <+> parens (text (w ++ "_bind")
        <+> parens (text $ "s::'a " ++ w) <+> text "t") <+> text "u"
        <+> equals <+> text (w ++ "_bind s")
        <+> parens (text "%x." <+>
                 text (w ++ "_bind") <+> text "(t x) u"))
    $+$ text "sorry "
  etaInjLemma w = text lemmaS <+> text (w ++ "_eta_inj:")
        <+> doubleQuotes (parens (text $ w ++ "_eta::'a => 'a " ++ w)
             <+> text "x"
             <+> equals <+> text (w ++ "_eta y")
             <+> text "==>" <+> text "x = y")
    $+$ text "sorry "

prnThymorph :: Doc -> String -> String -> TName -> [(String, String)]
            -> [(String, String)] -> Doc
prnThymorph nm xn tn t ts ws = let qual s = tn ++ "." ++ s in
     text "thymorph" <+> nm <+> colon <+>
            text xn <+> cfun <+> text tn
     $+$ text "  maps" <+> brackets
       (hcat [ parens $ doubleQuotes (text b <+> text a) <+> mapsto
               <+> doubleQuotes (text b <+> text (qual t))
             | (a, b) <- ts])
     $+$ brackMapList qual ws

brackMapList :: (String -> String) -> [(String, String)] -> Doc
brackMapList f ws = brackets $ hsep $ punctuate comma
  [ parens $ doubleQuotes (text a) <+> mapsto <+> doubleQuotes (text $ f b)
  | (a, b) <- ws]

-- filter out types that are given in the domain table
printTypeDecls :: BaseSig -> DomainTab -> Arities -> Doc
printTypeDecls bs odt ars =
    let dt = Map.fromList $ map (\ (t, _) -> (typeId t, [])) $ concat odt
    in vcat $ map (printTycon bs) $ Map.toList $ Map.difference ars dt

printTycon :: BaseSig -> (TName, [(IsaClass, [(Typ, Sort)])]) -> Doc
printTycon bs (t, arity') = case arity' of
  [] -> error "IsaPrint.printTycon"
  (_, rs) : _ ->
         if Set.member t
              $ Map.findWithDefault (error "Isabelle.printTycon") bs
                $ preTypes isaPrelude
         then empty else
            text typedeclS <+>
            (if null rs then empty else
             parens $ hsep $ punctuate comma
             $ map (text . ("'a" ++) . show . snd) $ number rs) <+> text t

-- | show alternative syntax (computed by comorphisms)
printAlt :: VName -> Doc
printAlt (VName _ altV) = case altV of
    Nothing -> empty
    Just (AltSyntax s is i) -> parens $ doubleQuotes (text s)
        <+> if null is then empty else text (show is) <+>
            if i == maxPrio then empty else text (show i)

instance Pretty Sign where
    pretty = printSign

-- | a dummy constant table with wrong types
constructors :: DomainTab -> ConstTab
constructors = Map.fromList . map (\ v -> (v, noTypeT))
               . concatMap (map fst . snd) . concat

printMonSign :: Sign -> Doc
printMonSign sig = let ars = arities $ tsig sig
                in
    printMonArities (theoryName sig) ars

printSign :: Sign -> Doc
printSign sig = let dt = ordDoms $ domainTab sig
                    ars = arities $ tsig sig
                in
    printAbbrs (abbrs $ tsig sig) $++$
    printTypeDecls (baseSig sig) dt ars $++$
    printDefinitions (defs $ tsig sig) $++$
    printFunctions (funs $ tsig sig) $++$
    printLocales (locales $ tsig sig) $++$
    printClassrel (classrel $ tsig sig) $++$
    printDomainDefs dt $++$
    printConstTab (Map.difference (constTab sig)
                  $ constructors dt) $++$
    (if showLemmas sig
         then showCaseLemmata dt else empty)
    where
    printAbbrs tab = if Map.null tab then empty else text typesS
                     $+$ vcat (map printAbbr $ Map.toList tab)
    printAbbr (n, (vs, t)) = case vs of
        [] -> empty
        [x] -> text ('\'' : x)
        _ -> parens $ hsep $ punctuate comma $
                                   map (text . ('\'' :)) vs
      <+> text n <+> equals <+> doubleQuotes (printType t)
    printConstTab tab = if Map.null tab then empty else text constsS
                        $+$ vcat (map printConst $ Map.toList tab)
    printConst (vn, t) = text (new vn) <+> doubleColon <+>
                          doubleQuotes (printType t) <+> printAlt vn
    isDomain = case baseSig sig of
               HOLCF_thy -> True
               HsHOLCF_thy -> True
               MHsHOLCF_thy -> True
               _ -> False
    printDomainDefs dtDefs = vcat $ map printDomainDef dtDefs
    printDomainDef dts = if null dts then empty else
        text (if isDomain then domainS else datatypeS)
        <+> andDocs (map printDomain dts)
    printDomain (t, ops) =
       printTyp (if isDomain then Quoted else Null) t <+> equals <+>
       fsep (bar $ map printDOp ops)
    printDOp (vn, args) = let opname = new vn in
       text (if any isSpace opname then show opname else opname)
       <+> hsep (map (printDOpArg opname) $ number args)
       <+> printAlt vn
    printDOpArg o (a, i) = let
      d = case a of
            TFree _ _ -> printTyp Null a
            _ -> doubleQuotes $ printTyp Null a
      in if isDomain then
           parens $ text "lazy" <+>
               text (o ++ "_" ++ show i) <> doubleColon <> d
           else d
    showCaseLemmata dtDefs = text (concatMap showCaseLemmata1 dtDefs)
    showCaseLemmata1 = concatMap showCaseLemma
    showCaseLemma (_, []) = ""
    showCaseLemma (tyCons, c : cns) =
      let cs = "case caseVar of" ++ sp
          sc b = showCons b c ++ concatMap (("   | " ++) . showCons b) cns
          clSome = sc True
          cl = sc False
          showCons b (VName {new = cName}, args) =
            let pat = cName ++ concatMap ((sp ++) . showArg) args
                            ++ sp ++ "=>" ++ sp
                term = showCaseTerm cName args
            in
               pat ++ if b then "Some" ++ sp ++ lb ++ term ++ rb ++ "\n"
                 else term ++ "\n"
          showCaseTerm name args = case name of
            "" -> sa
            n : _ -> toLower n : sa
            where sa = concatMap ((sp ++) . showArg) args
          showArg (TFree [] _) = "varName"
          showArg (TFree (n : ns) _) = toLower n : ns
          showArg (TVar v s) = showArg (TFree (unindexed v) s)
          showArg (Type [] _ _) = "varName"
          showArg (Type m@(n : ns) _ s) =
            if elem m ["typeAppl", "fun", "*"]
               then concatMap showArg s
               else toLower n : ns
          showName (TFree v _) = v
          showName (TVar v _) = unindexed v
          showName (Type n _ _) = n
          proof' = "apply (case_tac caseVar)\napply (auto)\ndone\n"
      in
        lemmaS ++ sp ++ "case_" ++ showName tyCons ++ "_SomeProm" ++ sp
                ++ "[simp]:\"" ++ sp ++ lb ++ cs ++ clSome ++ rb ++ sp
                ++ "=\n" ++ "Some" ++ sp ++ lb ++ cs ++ cl ++ rb ++ "\"\n"
                ++ proof'

instance Pretty Sentence where
    pretty = printSentence

sp :: String
sp = " "

rb :: String
rb = ")"

lb :: String
lb = "("

-- Pretty printing of proofs

instance Pretty IsaProof where
    pretty = printIsaProof

printIsaProof :: IsaProof -> Doc
printIsaProof (IsaProof p e) = fsep $ map pretty p ++ [pretty e]

instance Pretty ProofCommand where
    pretty = printProofCommand

printProofCommand :: ProofCommand -> Doc
printProofCommand pc =
    case pc of
      Apply pms plus ->
          let plusDoc = if plus then text "+" else empty
          in text applyS <+> parens
                              (sepByCommas $ map pretty pms) <> plusDoc
      Using ls -> text usingS <+> fsep (map text ls)
      Back -> text backS
      Defer x -> text deferS <+> pretty x
      Prefer x -> text preferS <+> pretty x
      Refute -> text refuteS

instance Pretty ProofEnd where
    pretty = printProofEnd

printProofEnd :: ProofEnd -> Doc
printProofEnd pe =
    case pe of
      By pm -> text byS <+> parens (pretty pm)
      DotDot -> text dotDot
      Done -> text doneS
      Oops -> text oopsS
      Sorry -> text sorryS

instance Pretty Modifier where
    pretty = printModifier

printModifier :: Modifier -> Doc
printModifier m =
    case m of
      No_asm -> text "no_asm"
      No_asm_simp -> text "no_asm_simp"
      No_asm_use -> text "no_asm_use"

instance Pretty ProofMethod where
    pretty = printProofMethod

printProofMethod :: ProofMethod -> Doc
printProofMethod pm =
    case pm of
      Auto -> text autoS
      Simp -> text simpS
      AutoSimpAdd m names -> let modDoc = case m of
                                            Just mod' -> parens $ pretty mod'
                                            Nothing -> empty
                             in fsep $ [text autoS, text simpS, modDoc,
                                             text "add:"] ++ map text names
      SimpAdd m names -> let modDoc = case m of
                                        Just mod' -> parens $ pretty mod'
                                        Nothing -> empty
                         in fsep $ [text simpS, modDoc, text "add:"] ++
                            map text names
      Induct var -> text inductS <+> doubleQuotes (printTerm var)
      CaseTac t -> text caseTacS <+> doubleQuotes (printTerm t)
      SubgoalTac t -> text subgoalTacS <+> doubleQuotes (printTerm t)
      Insert ts -> fsep (text insertS : map text ts)
      Other s -> text s
