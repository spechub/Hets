{- |
Module      :  $Header$
Description :  printing Isabelle entities
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
    ) where

import Isabelle.IsaSign
import Isabelle.IsaConsts
import Isabelle.IsaProofPrint ()

import Common.AS_Annotation
import qualified Data.Map as Map
import Common.Doc hiding (bar)
import Common.DocUtils

import Data.Char
import Data.List

printIsaTheory :: String -> Sign -> [Named Sentence] -> Doc
printIsaTheory tn sign sens = let
    b = baseSig sign
    bs = showBaseSig b
    ld = "$HETS_LIB/Isabelle/"
    use = text usesS <+> doubleQuotes (text $ ld ++ "prelude")
    in text theoryS <+> text tn
    $+$ text importsS <+> (if case b of
        Main_thy -> False
        HOLCF_thy -> False
        _ -> True then doubleQuotes $ text $ ld ++ bs else text bs)
    $+$ use
    $+$ text beginS
    $++$ printTheoryBody sign sens
    $++$ text endS

printTheoryBody :: Sign -> [Named Sentence] -> Doc
printTheoryBody sig sens =
    callML "initialize" (brackets $ sepByCommas
      $ map (text . show . Quote . senAttr)
      $ filter (\ s -> not (isConstDef s || isRecDef s || isInstance s)
                && senAttr s /= "") sens)
    $++$ printSign sig
    $++$ printNamedSentences sens
    $++$ printMonSign sig

printNamedSentences :: [Named Sentence] -> Doc
printNamedSentences sens = case sens of
  [] -> empty
  s : r
    | isIsaAxiom s ->
      let (axs, rest) = span isAxiom sens in
      text axiomsS $+$ vsep (map printNamedSen axs)
      $++$ vcat (map ( \ a -> text declareS <+> text (senAttr a)
                       <+> brackets (text simpS))
                $ filter ( \ a -> case sentence a of
                      b@Sentence{} -> isSimp b && senAttr a /= ""
                      _ -> False) axs)
      $++$ printNamedSentences rest
    | isConstDef s ->
      let (defs, rest) = span isConstDef sens in
      text defsS $+$ vsep (map printNamedSen defs)
      $++$ printNamedSentences rest
    | True ->
      printNamedSen s $++$ (case senAttr s of
        n | n == "" || isRecDef s -> empty
          | True -> callML "record" (text $ show $ Quote n))
      $++$ printNamedSentences r

callML :: String -> Doc -> Doc
callML fun args =
    text mlS <+> doubleQuotes (fsep [text ("Header." ++ fun), args])

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

----------------------- Printing functions -----------------------------

showBaseSig :: BaseSig -> String
showBaseSig = reverse . drop 4 . reverse . show

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
                                then v  else '\'' : v
        c = printSort s
     in if null s then d else case a of
         Quoted -> d <> doubleColon <> if null
                     $ tail s then c else doubleQuotes c
         Unquoted -> d <> doubleColon <> c
         Null -> d, 1000)
 TVar iv s -> printTypeAux a $ TFree ("?\'" ++ unindexed iv) s
 Type name _ args -> case args of
    [t1, t2] | elem name [prodS, sProdS, funS, cFunS, lFunS, sSumS] ->
       printTypeOp a name t1 t2
    _  -> ((case args of
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
                    [ (funS, (1,0))
                    , (cFunS, (1,0))
                    , (lFunS, (1,0))
                    , (sSumS, (11, 10))
                    , (prodS, (21, 20))
                    , (sProdS, (21, 20))
                    , (lProdS, (21, 20))
                    ]
        d3 = if i1 < l then parens d1 else d1
        d4 = if i2 < r then parens d2 else d2
    in (d3 <+> text name <+> d4, r)

and_docs :: [Doc] -> Doc
and_docs ds = vcat $ prepPunctuate (text andS <> space) ds

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
  Instance {} -> d
  _ -> let dd = doubleQuotes d in
       if isRefute s then text lemmaS <+> text lab <+> colon
              <+> dd $+$ text refuteS
       else if null lab then dd else fsep[ (case s of
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
  TypeDef nt td pr ->  text typedefS
                   <+> printType nt
                   <+> equals
                   <+> doubleQuotes(printSetDecl td)
                   $+$ pretty pr
  RecDef kw xs -> text kw <+>
     and_docs (map (vcat . map (doubleQuotes . printTerm)) xs)
  Instance { tName = t, arityArgs = args, arityRes = res, instProof = prf } ->
      text instanceS <+> text t <> doubleColon <> (case args of
        []  -> empty
	_ -> parens $ hsep $ punctuate comma $
	     map (printSortAux True) args)
        <+> printSortAux True res <+> pretty prf
  Sentence { isRefuteAux = b, metaTerm = t } -> printPlainMetaTerm (not b) t
  ConstDef t -> printTerm t

printSetDecl :: SetDecl -> Doc
printSetDecl (SubSet v t f) =
  braces $ printTerm v <> doubleColon <> printType t <> dot <> printTerm f

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
        Const (VName n (Just (AltSyntax s is i))) _ ->
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
            Hide _ _ _ -> dvn
            Disp w _ _ -> parens $ dvn <+> doubleColon <+> printType w
      in case altSyn vn of
          Nothing -> (nvn, maxPrio)
          Just (AltSyntax s is i) -> if b && null is then
              (fsep $ replaceUnderlines s [], i) else (nvn, maxPrio)
    Free vn -> (text $ new vn, maxPrio)
    Abs v t c -> ((text $ case c of
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
                        []  -> error "IsaPrint, printTrm"
                        [a] -> printTrm b a
                        a:aa -> printTrm b $ App (App
                                  lpairTerm a $ IsCont False)
                                     (Tuplex aa c) (IsCont False)
    App f a c -> printMixfixAppl b c f [a]

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
    '\'': r@(q : s) -> if q `elem` "_/'()"
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

printClassrel :: Classrel -> Doc
printClassrel = vcat . map printClassR . (orderCDecs . Map.toList)

printClassR :: (IsaClass,[IsaClass]) -> Doc
printClassR (y,ys) = case ys of
  [] -> empty
  z : zs -> text axclassS <+> printClass y <+> less <+> printClass z
    $+$ vcat (map (\ x ->
                  text instanceS <+> printClass y <+> less <+>
                                  printClass x <+> text dotDot) zs)

orderCDecs :: [(IsaClass, Maybe [IsaClass])] -> [(IsaClass,[IsaClass])]
orderCDecs ls = let
      ws = [(x,ys) | (x,Just ys) <- ls]
   in quickSort crord ws
 where
   crord m n = elem (fst n) (snd m)

printMonArities :: String -> Arities -> Doc
printMonArities tn = vcat . map ( \ (t, cl) ->
                  vcat $ map (printThMorp tn t) cl) . Map.toList

printThMorp :: String -> TName -> (IsaClass, [(Typ, Sort)]) -> Doc
printThMorp tn t xs = case xs of
   (IsaClass "Monad", _) ->
      if (isSuffixOf "_mh" tn) || (isSuffixOf "_mhc" tn)
      then printMInstance tn t
      else error "IsaPrint, printInstance: monads not supported"
   _ -> empty

printMInstance :: String -> TName -> Doc
printMInstance tn t = let nM = text (t ++ "_tm")
                          nM2 = text (t ++ "_tm2")
 in prnThymorph nM "MonadType" tn t [("MonadType.M","'a")] []
    $+$ text "t_instantiate MonadOps mapping" <+> nM
    $+$ text "renames:" <+>
       brackMapList (\x -> t ++ "_" ++ x)
            [("MonadOpEta.eta","eta"),("MonadOpBind.bind","bind")]
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
    $++$ prnThymorph nM2 "MonadAxms" tn t [("MonadType.M","'a")]
        [("MonadOpEta.eta",(t ++ "_eta")),
         ("MonadOpBind.bind",(t ++ "_bind"))]
    $+$ text "t_instantiate Monad mapping" <+> nM2
    $+$ text "renames:" <+>
       brackMapList (\x -> t ++ "_" ++ x)
           [("Monad.kapp","kapp"),
            ("Monad.lift","lift"),
            ("Monad.lift","lift"),
            ("Monad.mapF","mapF"),
            ("Monad.bind'","mbbind"),
            ("Monad.joinM","joinM"),
            ("Monad.kapp2","kapp2"),
            ("Monad.kapp3","kapp3"),
            ("Monad.lift2","lift2"),
            ("Monad.lift3","lift3")]
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
        <+> doubleQuotes ((text $ w ++ "_bind")
        <+> parens ((text $ w ++ "_bind")
        <+> parens (text $ "s::'a " ++ w) <+> text "t") <+> text "u"
        <+> equals <+> text (w ++ "_bind s")
        <+> parens ((text "%x.") <+>
                 (text $ w ++ "_bind") <+> text "(t x) u"))
    $+$ text "sorry "
  etaInjLemma w = text lemmaS <+> text (w ++ "_eta_inj:")
        <+> doubleQuotes (parens (text $ w ++ "_eta::'a => 'a " ++ w)
             <+> text "x"
             <+> equals <+> (text $ w ++ "_eta y")
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

brackMapList :: (String -> String) -> [(String,String)] -> Doc
brackMapList f ws = brackets $ hsep $ punctuate comma
  [ parens $ doubleQuotes (text a) <+> mapsto <+> doubleQuotes (text $ f b)
  | (a, b) <- ws]

-- filter out types that are given in the domain table
printTypeDecls :: DomainTab -> Arities -> Doc
printTypeDecls odt ars =
    let dt = Map.fromList $ map (\ (t, _) -> (typeId t, [])) $ concat odt
    in vcat $ map printTycon $ Map.toList $ Map.difference ars dt

printTycon :: (TName, [(IsaClass, [(Typ, Sort)])]) -> Doc
printTycon (t, arity') = case arity' of
  [] -> error "IsaPrint.printTycon"
  (_, rs) : _ ->
         if elem t ["lBool","intT","integerT","charT","ratT","lString"
                    ,"unitT","unit","bool","int","char","rat","string"
                    ,"lOrdering","sOrdering","either","*"
                    ,"llist","list","lprod","lEither","lMaybe","option"]
         then empty else
            text typedeclS <+>
            (let arity = length rs in if arity > 0
             then parens $ hsep $ punctuate comma
                      $ map (text . ("'a" ++) . show) [1..arity]
             else empty) <+> text t

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

cmpDomainEntries :: [(Typ, [(VName, [Typ])])] -> [(Typ, [(VName, [Typ])])]
                 -> Ordering
cmpDomainEntries l1 l2 = let
    t1 = map fst l1
    t2 = map fst l2
    a1 = concatMap (concatMap snd . snd) l1
    a2 = concatMap (concatMap snd . snd) l2
    in case (null $ intersect t1 a2, null $ intersect t2 a1) of
       (True, False) -> GT
       (False, True) -> LT
       (True, True) -> EQ
       (False, False) -> error "cmpDomainEntries"

printSign :: Sign -> Doc
printSign sig = let dt = sortBy cmpDomainEntries $ domainTab sig
                    ars = arities $ tsig sig
                in
    printAbbrs (abbrs $ tsig sig) $++$
    printTypeDecls dt ars $++$
    printClassrel (classrel $ tsig sig) $++$
    printDomainDefs dt $++$
    printConstTab (Map.difference (constTab sig)
                  $ constructors dt) $++$
    (if showLemmas sig
         then showCaseLemmata (domainTab sig) else empty)
    where
    printAbbrs tab = if Map.null tab then empty else text typesS
                     $+$ vcat (map printAbbr $ Map.toList tab)
    printAbbr (n, (vs, t)) = (case vs of
       [] -> empty
       [x] -> text ("\'" ++ x)
       _ -> parens $ hsep $ punctuate comma $
                                   map (\x -> text $ "\'" ++ x) vs)
       <+> (text $ n) <+> equals <+> (doubleQuotes $ printType t)
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
        <+> and_docs (map printDomain dts)
    printDomain (t, ops) =
       printTyp (if isDomain then Quoted else Null) t <+> equals <+>
       hsep (bar $ map printDOp ops)
    printDOp (vn, args) = let opname = new vn in
       text opname <+> hsep (map (printDOpArg opname)
                            $ zip args [1 :: Int .. ])
       <+> printAlt vn
    printDOpArg o (a, i) = let
      d = case a of
            TFree _ _ -> printTyp Null a
            _         -> doubleQuotes $ printTyp Null a
      in if isDomain then
           parens $ text "lazy" <+>
               text (o ++ "_" ++ show i) <> doubleColon <> d
           else d
    showCaseLemmata dtDefs = text (concat $ map showCaseLemmata1 dtDefs)
    showCaseLemmata1 dts = concat $ map showCaseLemma dts
    showCaseLemma (_, []) = ""
    showCaseLemma (tyCons, (c : cns)) =
      let cs = "case caseVar of" ++ sp
          sc b = showCons b c ++ (concat $ map (("   | " ++)
                                                . (showCons b)) cns)
          clSome = sc True
          cl = sc False
          showCons b ((VName {new=cName}), args) =
            let pat = cName ++ (concat $ map ((sp ++) . showArg) args)
                            ++ sp ++ "=>" ++ sp
                term = showCaseTerm cName args
            in
               if b then pat ++ "Some" ++ sp ++ lb ++ term ++ rb ++ "\n"
                 else pat ++ term ++ "\n"
          showCaseTerm name args = if null name then sa
                                     else [toLower (head name)] ++ sa
            where sa = (concat $ map ((sp ++) . showArg) args)
          showArg (TFree [] _) = "varName"
          showArg (TFree (n:ns) _) = [toLower n] ++ ns
          showArg (TVar v s) = showArg (TFree (unindexed v) s)
          showArg (Type [] _ _) = "varName"
          showArg (Type m@(n:ns) _ s) =
            if m == "typeAppl" || m == "fun" || m == "*"
               then concat $ map showArg s
               else [toLower n] ++ ns
          showName (TFree v _) = v
          showName (TVar v _) = unindexed v
          showName (Type n _ _) = n
          proof = "apply (case_tac caseVar)\napply (auto)\ndone\n"
      in
        lemmaS ++ sp ++ "case_" ++ showName tyCons ++ "_SomeProm" ++ sp
                ++ "[simp]:\"" ++ sp ++ lb ++ cs ++ clSome ++ rb ++ sp
                ++ "=\n" ++ "Some" ++ sp ++ lb ++ cs ++ cl ++ rb ++ "\"\n"
                ++ proof

instance Pretty Sentence where
    pretty = printSentence

sp :: String
sp = " "

rb :: String
rb = ")"

lb :: String
lb = "("
