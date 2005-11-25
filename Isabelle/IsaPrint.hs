{- |
Module      :  $Header$
Copyright   :  (c) University of Cambridge, Cambridge, England
               adaption (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Printing functions for Isabelle logic.
-}
{-
  todo: brackets in (? x . p x) ==> q
  properly construct docs
-}

module Isabelle.IsaPrint
    ( showBaseSig
    , printNamedSen
    ) where

import Isabelle.IsaSign
import Isabelle.IsaConsts
import Common.Lib.Pretty
import Common.AS_Annotation
import Common.PrettyPrint
import Common.PPUtils
import qualified Common.Lib.Map as Map

import Data.Char
import Data.List
------------------- Printing functions -------------------

showBaseSig :: BaseSig -> String
showBaseSig = reverse . drop 4 . reverse . show

printClass :: IsaClass -> Doc
printClass (IsaClass x) = text x

printSort :: Sort -> Doc
printSort l = case l of
    [c] -> printClass c
    _ -> braces . hsep . punctuate comma $ map printClass l

data SynFlag = Unquoted | Null

doubleColon :: Doc
doubleColon = text "::"

printType :: Typ -> Doc
printType = printTyp Unquoted

printTyp :: SynFlag -> Typ -> Doc
printTyp a = fst . printTypeAux a

printTypeAux :: SynFlag -> Typ -> (Doc, Int)
printTypeAux a t = case t of
 (TFree v s) -> (let d = text $ if isPrefixOf "\'" v || isPrefixOf "?\'" v
                                then v  else '\'' : v
                 in if null s then d else case a of
   Unquoted -> d <> doubleColon <> printSort s
   Null -> d, 1000)
 (TVar iv s) -> printTypeAux a $ TFree ("?\'" ++ unindexed iv) s
 (Type name _ args) -> case args of
   [t1, t2] | elem name [prodS, sProdS, funS, cFunS, sSumS] ->
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
                    , (sSumS, (11, 10))
                    , (prodS, (21, 20))
                    , (sProdS, (21, 20))
                    ]
        d3 = if i1 < l then parens d1 else d1
        d4 = if i2 < r then parens d2 else d2
    in (d3 <+> text name <+> d4, r)

and_docs :: [Doc] -> Doc
and_docs ds = vcat $ prepPunctuate (text "and ") ds

-- | printing a named sentence
printNamedSen :: Named Sentence -> Doc
printNamedSen NamedSen { senName = lab, sentence = s } =
  let d = printSentence s in case s of
  RecDef _ _ -> d
  _ -> let dd = doubleQuotes d in if null lab then dd else text (case s of
    ConstDef _ -> lab ++ "_def"
    Sentence _ -> lab
    _ -> "theorem " ++ lab) <+> colon <+> dd

-- | sentence printing
printSentence :: Sentence -> Doc
printSentence s = case s of
  RecDef kw xs -> text kw <+>
     and_docs (map (vcat . map (doubleQuotes . printTerm)) xs)
  _ -> case senTerm s of
      IsaEq (Const vn y) t ->  text (new vn) <+> doubleColon
                      <+> printType y <+> text "==" <+> printOUTerm t
      t -> printTerm t

-- | omits type of outer abstraction
printOUTerm :: Term -> Doc
printOUTerm t = case t of
  (Abs v _ tm l) -> parens $ (text $ case l of
     NotCont -> "%"
     IsCont -> "LAM") <+> printTerm v <> text "." <+> printOUTerm tm
  _ -> printTerm t

-- | print plain term
printTerm :: Term -> Doc
printTerm = printPlainTerm

printPlainTerm :: Term -> Doc
printPlainTerm = fst . printTrm

printParenTerm :: Int -> Term -> Doc
printParenTerm i t = case printTrm t of
    (d, j) -> if j < i then parens d else d

printTrm :: Term -> (Doc, Int)
printTrm trm = case trm of
    Const vn _ -> case altSyn vn of
        Nothing -> (text $ new vn, maxPrio)
        Just (AltSyntax s is i) -> if null is then 
            (replaceUnderlines s [], i) else (text $ new vn, i)
    Free vn _ -> (text $ new vn, maxPrio)
    Var (Indexname _ _) _ -> error "Isa.Term.Var not used"
    Bound _ -> error "Isa.Term.Bound not used"
    Abs v _ b c -> ((text $ case c of
        NotCont -> "%"
        IsCont -> "LAM") <+> printPlainTerm v <> text "." 
                    <+> printPlainTerm b, lowPrio)
    If i t e NotCont -> (text "if" <+> printPlainTerm i <+> 
                        text "then" <+> printPlainTerm t <+>
                        text "else" <+> printPlainTerm e, 
                        lowPrio)
    If i t e IsCont -> (text "If" <+> printPlainTerm i <+> 
                        text "then" <+> printPlainTerm t <+>
                        text "else" <+> printPlainTerm e <+> text "fi", 
                        maxPrio)
    Case e ps -> (text "case" <+> printPlainTerm e <+> text "of"
                  $$ vcat (punctuate (space <> text "|") $ 
                         map (\ (p, t) -> printPlainTerm p <+> text "=>"
                                       <+> printPlainTerm t) ps), lowPrio)
    Let es i -> (text "let" <+> 
           vcat (punctuate semi $ 
                 map (\ (p, t) -> printPlainTerm p <+> text "="
                               <+> printPlainTerm t) es) 
           <+> text "in" <+> printPlainTerm i, lowPrio)
    IsaEq t1 t2 -> (printParenTerm (isaEqPrio + 1) t1 <+> text "=="
                   <+> printParenTerm isaEqPrio t2, isaEqPrio)
    Tuplex cs c -> ((case c of 
        NotCont -> parens
        IsCont -> \ d -> text "<" <+> d <+> text ">") $ 
                        fsep (punctuate comma $ map printPlainTerm cs)
                    , maxPrio)
    Fix t -> (text "fix $" <+> printParenTerm maxPrio t, maxPrio - 1)
    Bottom -> (text "UU", maxPrio)
    Wildcard -> error "Isa.Term.Wildcard not used"
    Paren t -> (parens $ printPlainTerm t, maxPrio)
    App f a c -> case f of 
        Const (VName _ (Just (AltSyntax s [j] i))) _
            -> (replaceUnderlines s [printParenTerm j a] , i)
        Const vn _ | new vn `elem` [allS, exS, ex1S] -> case a of
            Abs v _ b _ -> (text (new vn) <+> printPlainTerm v
                    <> text "." 
                    <+> printPlainTerm b, lowPrio)
            _ -> error "printTrm.quantor"
        _ -> (printParenTerm (maxPrio - 1) f <+>
                    (case c of
                       NotCont -> empty
                       IsCont -> text "$")
                    <+> printParenTerm maxPrio a, maxPrio - 1)
    MixfixApp f args c -> case f of 
        Const (VName _ (Just (AltSyntax s is i))) _ | length is == length args
            -> (replaceUnderlines s $ zipWith printParenTerm is args, i)
        MixfixApp g margs@(_ : _) _ -> printTrm $ MixfixApp g (margs ++ args) c
        _ -> case args of 
             [] -> printTrm f
             a : l -> printTrm (MixfixApp (App f a c) l c)

replaceUnderlines :: String -> [Doc] -> Doc
replaceUnderlines str l = case str of
    "" -> empty
    '\'': r@(q : s) -> if q `elem` "_/'()" 
                       then text [q] <> replaceUnderlines s l
                       else text "'" <> replaceUnderlines r l
    '_' : r -> case l of
                  h : t -> h <> replaceUnderlines r t
                  _ -> error "replaceUnderlines"
    q : r -> if q `elem` "()/" then replaceUnderlines r l
             else text [q] <> replaceUnderlines r l

-- end of term printing

printClassrel :: Classrel -> Doc
printClassrel = vcat . map ( \ (t, cl) -> case cl of
     Nothing -> empty
     Just x -> text "axclass" <+> printClass t <+> text "<" <+>
       (if null x  then text "pcpo" else printSort x)) . Map.toList

printArities :: Arities -> Doc
printArities = vcat . map ( \ (t, cl) ->
                  vcat $ map (printInstance t) cl) . Map.toList

printInstance :: TName -> (IsaClass, [(Typ, Sort)]) -> Doc
printInstance t xs = text "instance" <+> text t <> doubleColon <>
    (case snd xs of
     [] -> empty
     ys -> parens $ hsep $ punctuate comma
           $ map (doubleQuotes . printSort . snd) ys)
    <> printClass (fst xs) $$ text "by intro_classes"

printTypeDecls :: Sign -> Doc
printTypeDecls sig =
    Map.foldWithKey (printTycon sig) empty $ arities $ tsig sig

printTycon :: Sign -> TName -> [(IsaClass, [(Typ, Sort)])] -> Doc -> Doc
printTycon sig t arity' rest =
              let arity = if null arity' then
                          error "IsaPrint.printText0 (TypeSig)"
                                else length (snd $ head arity') in
            if dtyp sig t then empty else
            text "typedecl" <+>
            (if arity > 0
             then parens $ hsep (map (text . ("'a"++) . show) [1..arity])
             else empty) <+> text t $$ rest

dtyp :: Sign -> TName -> Bool
dtyp sig t = elem t $
         concat [map (typeId . fst) x | x <- domainTab sig]

-- | show alternative syntax (computed by comorphisms)
printAlt :: VName -> Doc
printAlt (VName _ altV) = case altV of
    Nothing -> empty
    Just (AltSyntax s is i) -> parens $ doubleQuotes (text s)
        <+> if null is then empty else text (show is) <+> 
            if i == maxPrio then empty else text (show i)

instance PrettyPrint Sign where
  printText0 _ sig = 
    printTypeDecls sig $++$
    printClassrel (classrel $ tsig sig) $++$
    printDomainDefs (domainTab sig) $++$
    printConstTab (constTab sig) $++$
    (if showLemmas sig then showCaseLemmata (domainTab sig) else empty) $++$
                                   -- this may print an "o"
    printArities (arities $ tsig sig)
    where
    printConstTab tab = if Map.null tab then empty else text "consts"
                        $$ vcat (map printConst $ Map.toList tab)
    printConst (vn, t) = text (new vn) <+> doubleColon <+>
                          doubleQuotes (printType t) <+> printAlt vn
    isDomain = case baseSig sig of
               HOLCF_thy -> True
               HsHOLCF_thy -> True
               _ -> False
    printDomainDefs dtDefs = vcat $ map printDomainDef dtDefs
    printDomainDef dts = if null dts then empty else
        text (if isDomain then "domain" else "datatype")
        <+> and_docs (map printDomain dts)
    printDomain (t, ops) =
       printType t <+> equals <+>
       hsep (punctuate (text " |") $ map printDOp ops)
    printDOp (vn, args) = let opname = new vn in
       text opname <+> hsep (map (printDOpArg opname)
                            $ zip args $ reverse [1 .. length args])
       <+> printAlt vn
    printDOpArg o (a, i) = let
      d = case a of
            TFree _ _ -> printTyp Null a
            _         -> doubleQuotes $ printTyp Null a
      in if isDomain then
           parens $ text (o ++ "_" ++ show i) <> doubleColon <> d
           else d
    showCaseLemmata dtDefs = text (concat $ map showCaseLemmata1 dtDefs)
    showCaseLemmata1 dts = concat $ map showCaseLemma dts
    showCaseLemma (_, []) = ""
    showCaseLemma (tyCons, (c:cons)) =
      let cs = "case caseVar of" ++ sp
          sc b = showCons b c ++ (concat $ map (("   | " ++)
                                                . (showCons b)) cons)
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
        "lemma" ++ sp ++ "case_" ++ showName tyCons ++ "_SomeProm" ++ sp
                ++ "[simp]:\"" ++ sp ++ lb ++ cs ++ clSome ++ rb ++ sp
                ++ "=\n" ++ "Some" ++ sp ++ lb ++ cs ++ cl ++ rb ++ "\"\n"
                ++ proof

instance PrintLaTeX Sign where
    printLatex0 = printText0

instance PrintLaTeX Sentence where
  printLatex0 = printText0

instance PrettyPrint Sentence where
      printText0 _ = printSentence

sp :: String
sp = " "

rb :: String
rb = ")"

lb :: String
lb = "("
