{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories.
-}

module OWL_DL.Print where

import Common.Doc
import Common.DocUtils

import OWL_DL.Sign
import OWL_DL.AS

import qualified Data.Set as Set
import qualified Data.Map as Map

instance Pretty Sign where
    pretty = printSign

printSign :: Sign -> Doc
printSign (Sign _ p2 p3 p4 p5 p6 _ p8 p9 p10) =
    text "namespaces " $+$ printNamespace p10 $+$
    text "concepts" <+> setToDocF p2 $+$
    text "primaryConcepts " <+> setToDocF p3 $+$
    text "datatypes " <+> setToDocF p4 $+$
    text "indvidual_valued_roles " <+> setToDocF p5 $+$
    text "data_valued_roles " <+> setToDocF p6 $+$
    text "individuals " <+> setToDocF p8 $+$
    text "sign_axioms" $+$ vcat (setToDocs p9)

instance Pretty URIreference where
    pretty = printURIreference

printURIreference :: URIreference -> Doc
printURIreference (QN prefix localpart uri)
    | localpart == "_" = text $ show "_"
    | null prefix = if null uri then
                           text localpart
                           else text $ show (uri ++ ":" ++ localpart)
    | otherwise =   text $ show ( prefix ++ ":" ++ localpart)

printNamespace :: Namespace -> Doc
printNamespace nsMap =
    vcat $ map pp (Map.toList nsMap)
       where pp :: (String, String) -> Doc
             pp (s1,s2) = text s1 <> defn <> text s2

instance Pretty Sentence where
    pretty = printSentence

printSentence :: Sentence -> Doc
printSentence sent = case sent of
    OWLAxiom axiom -> printAxiom axiom
    OWLFact fact   -> printFact fact

-- not necessary
instance Pretty Ontology where
    pretty = printOntology

printOntology :: Ontology -> Doc
printOntology (Ontology maybeID directives ns) =
    text "Ontology" <+>
          (case maybeID of
             Just oid -> printURIreference oid
             _        -> text "anomie"
            ) $+$
    (fsep $ map printDirective directives) $+$
    printNamespace ns

instance Pretty Directive where
    pretty = printDirective

printDirective :: Directive -> Doc
printDirective = text . show

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
    Class cid _ _ _ descs ->
      listToDocV (printDescription (-1)) cid descs
    EnumeratedClass cid _ _ iids ->
      parens (text "forall ((x owl:Thing))" $+$
                          (printDescription (-1) cid $ OneOfDes iids))
    DisjointClasses desc1 desc2 _ ->
      parens (text "forall ((x owl:Thing))" <+>
              parens (text "not" <+> parens (text "and" <+>
                 printDescription (-1) emptyQN desc1 <+>
                 text "x" <+>
                 printDescription (-1) emptyQN desc2 <+> text "x")))
    EquivalentClasses desc1 descs ->
      listToDocV
          (\x y ->
          case y of
          DC cid2 ->
            parens (text "forall ((x owl:Thing))" <+>
                    parens (text "iff" <>
                    printDescription (-1) emptyQN x <+>
                    text "x" <+> printURIreference cid2 <+>
                    text "x"))
          _      ->
              case x of
                DC cid1 ->
                   parens (text "forall ((x owl:Thing))" $+$
                           printDescription (-1) cid1 y)
                _       -> error ("EquivalentClasses Error:" ++ (show axiom))
          ) desc1 descs
    Datatype dID _ _ ->
      printURIreference dID
    DEquivalentProperties dpID1 dpID2 _ ->
            parens (text "forall ((x owl:Thing) (y owl:Thing))" <+>
                     parens (text "iff" <> printURIreference dpID1 <+>
                     text "x y" <+> printURIreference dpID2 <+>
                     text "x y"))
    IEquivalentProperties ipID1 ipID2 _ ->
            parens (text "forall ((x owl:Thing) (y owl:Thing))" <+>
                    parens (text "iff" <> printURIreference ipID1 <+>
                    text "x y" <+> printURIreference ipID2 <+>
                    text "x y"))
    DSubPropertyOf dpID1 dpID2 ->
            parens (text "forall ((x owl:Thing) (y rdfs:Lilteral))" <+>
                    parens (text "implies" <+>
                            parens (printURIreference dpID1 <+>
                                    text "x y") <+>
                            parens (printURIreference dpID2 <+>
                                    text "x y")))
    ISubPropertyOf ipID1 ipID2 ->
            parens (text "forall ((x owl:Thing) (y owl:Thing))" <+>
                    parens (text "implies" <+>
                            parens (printURIreference ipID1 <+>
                                    text "x y") <+>
                            parens (printURIreference ipID2 <+>
                                    text "x y")))
    ObjectProperty iid _ _ _ maybeInverse isSymmetric maybeFunc _ _ ->
      case maybeInverse of
        Just pid -> parens (text "forall ((x owl:Thing) (y owl:Thing))"
                            <+>  parens (text "iff" <+>
                                         parens (printURIreference iid <+>
                                                 text "x y") <+>
                                         parens (printURIreference pid <+>
                                                 text "y x")))
        _ -> if isSymmetric then
                parens (text "forall ((x owl:Thing) (y owl:Thing))"
                        <+>  parens (text "implies" <+>
                                     parens (printURIreference iid <+>
                                             text "x y") <+>
                                     parens (printURIreference iid <+>
                                             text "y x")))
               else
                 case maybeFunc of
                   Just InverseFunctional ->
                     parens (text ("forall ((x owl:Thing)" ++
                              "(y owl:Thing) (z owl:Thing))") <+>
                             parens (text "implies" $+$
                                     parens (text "and" <+>
                                              printURIreference iid <+>
                                              text "y z" $+$
                                              printURIreference iid <+>
                                              text "z x") $+$
                                     (parens $ text "= y z")))
                   Just Transitive ->
                     parens (text ("forall ((x owl:Thing)" ++
                              "(y owl:Thing) (z owl:Thing))") <+>
                             parens (text "implies" $+$
                                     parens (text "and" <+>
                                             printURIreference iid <+>
                                             text "x y" $+$
                                             printURIreference iid<+>
                                             text "y z") $+$
                                     parens (printURIreference iid <+>
                                             text "x z")))
                   _  -> text ""
    u -> text $ show u

instance Pretty SignAxiom where
    pretty = printSignAxiom

printSignAxiom :: SignAxiom -> Doc
printSignAxiom signAxiom = case signAxiom of
    Subconcept cid1 cid2 ->
      parens (text "forall ((x owl:Thing))" <+>
              parens (text "implies" <+>
                      parens (printURIreference cid1 <+> text "x") <+>
                      parens (printURIreference cid2 <+> text "x")))
    RoleDomain rid rdomains ->
      listToDocH
        (\x y -> parens (text "forall ((x owl:Thing) (y owl:Thing))" $+$
                         parens (text "implies" <+>
                                 parens (printURIreference x <+>
                                         text "x y") <+>
                                 (parens $ printRDomain y)))
        ) rid rdomains
    RoleRange rid rranges -> case head rranges of
      RDRange _ ->
        text "(forall ((x owl:Thing) (y rdfs:Literal))" $+$
        text "(implies (" <> printURIreference rid <+> text "x y)" $+$
        (if (length rranges > 1) then
           text "(or "
         else lparen) <>
        listToDocH form5 rid rranges $+$ text ")))"
      _         ->
        listToDocV
          (\x y -> text "(forall ((x owl:Thing) (y owl:Thing))" $+$
                   text "(implies (" <> printURIreference x <+>
                   text "x y) (" <> printRRange y <> text " y)" $+$
                   text "))")
          rid rranges
    FuncRole (rtype, rid) ->
      case rtype of
        IRole ->
          text "(forall ((x owl:Thing) (y owl:Thing) (z owl:Thing))" $+$
          text "(implies" $+$
          text "(and (" <> printURIreference rid <+>
          text "x y) (" <+> printURIreference rid <+> text "x z))" $+$
          text "(= y z)" $+$ text "))"
        DRole ->
          text "(forall ((x owl:Thing) (y rdfs:Literal) (z rdfs:Literal))" $+$
          text "(implies" $+$
          text "(and (" <> printURIreference rid <+>
          text "x y) (" <+> printURIreference rid <+> text "x z))" $+$
          text "(= y z)" $+$ text "))"
    Conceptmembership iID desc ->
      parens (printDescription 0 iID desc <+> printURIreference iID)

instance Pretty RDomain where
    pretty = printRDomain

printRDomain :: RDomain -> Doc
printRDomain (RDomain desc) =
    case desc of
      DC cid -> printURIreference cid <+> text "x"
      _      -> printDescription 0 emptyQN desc  -- ToDo: level hierachie

instance Pretty RRange where
    pretty = printRRange

printRRange :: RRange -> Doc
printRRange rRange = case rRange of
    RIRange desc -> printDescription 0 emptyQN desc -- ToDo: level hierachie
    RDRange dataRange -> printDataRange dataRange

instance Pretty DataRange where
    pretty = printDataRange

printDataRange :: DataRange -> Doc
printDataRange dr = case dr of
    DID dtID -> printURIreference dtID
    OneOfData dls ->
      parens ((text "DEBUG:forall ((x rdfs:Literal))") $+$
      (if allEqTypedLit dls then
             case head dls of
                 TypedL (_, drType) ->
                    (text "(iff (") <> (printURIreference drType) <+>
                    (text "x)")
                 _  -> error "false check datarange."
          else empty) $+$ (parens (text "or") <>
           parens (listToDocH form4 emptyQN dls)) <>
           (if allEqTypedLit dls then rparen else empty))
    RLit rdfLit   -> (text "rdf_literal") <+> (text rdfLit)
  where allEqTypedLit :: [DataLiteral] -> Bool
        allEqTypedLit [] = False
        allEqTypedLit (TypedL (_, ty):dls') = all check dls'
                where check :: DataLiteral -> Bool
                      check dl = case dl of
                          TypedL (_, t) -> if t == ty then True
                                           else False
                          _             -> False
        allEqTypedLit _ = False

instance Pretty DataLiteral where
    pretty = printDataLiteral

printDataLiteral :: DataLiteral -> Doc
printDataLiteral dl = case dl of
    TypedL (lf, uri) -> parens (text (lf ++ ":") <+>
                                     printURIreference uri)
    PlainL (lf, lt)  -> parens (text ("stringInLang '"++lf++" : "++lt))
    Plain lf         -> text lf
    RDFSL rdfLit     -> text rdfLit

-- default handler of restriction
instance Pretty Restriction where
    pretty = printRestriction

printRestriction :: Restriction -> Doc
printRestriction restr = case restr of
    DataRestriction dpID drcom drcoms ->
            printRestriction1 (-1) 0 dpID (drcom:drcoms)
    IndivRestriction ipID ircom ircoms ->
            printRestriction2 (-1) 0 ipID (ircom:ircoms)

printRestriction1 :: Int -> Int -> URIreference -> [Drcomponent] -> Doc
printRestriction1 _ _ _ [] = empty
printRestriction1  origVar tmpVar dpID (h:r) = case h of
    DRCAllValuesFrom dataRange ->
      parens (text "forall" <+> parens (text (choiceName tmpVar ++
                                                    " rdfs:Literal")) <+>
           parens ((text "implies") <> parens ((printURIreference dpID) <+>
                  (text ((choiceName origVar)++" "++(choiceName tmpVar)))) <+>
                        (printDataRange dataRange))) $+$
      (printRestriction1 origVar (tmpVar+1) dpID r)
    DRCSomeValuesFrom dataRange ->
      parens (text "exists" <+> parens (text (choiceName tmpVar ++
                                                    " rdfs:Literal")) <+>
          parens ((text "and") <> parens ((printURIreference dpID) <+>
                  (text ((choiceName origVar)++" "++(choiceName tmpVar)))) <+>
                       (printDataRange dataRange))) $+$
      (printRestriction1 origVar (tmpVar+1) dpID r)
    DRCValue dl ->
      (printURIreference dpID) <+> (text $ choiceName origVar ++ "r1") <+>
          (printDataLiteral dl) $+$
        (printRestriction1 origVar tmpVar dpID r)
    DRCCardinality cardinality ->
        (printCard origVar dpID cardinality) $+$
        (printRestriction1 origVar tmpVar dpID r)

printRestriction2 :: Int -> Int -> URIreference
                  -> [Ircomponent] -> Doc
printRestriction2 _ _ _ [] = empty
printRestriction2 origVar tmpVar ipID (h:r) = case h of
    IRCAllValuesFrom desc ->
      parens (text "forall" <+> parens (text $ (choiceName tmpVar ++
                                                    " owl:Thing")) <+>
           parens ((text "implies") <+> parens ((printURIreference ipID) <+>
                  (text ((choiceName origVar)++" "++(choiceName tmpVar)))) <+>
               (case desc of
                DC _ -> parens ((printDescription origVar ipID desc) <+>
                                (text $ choiceName tmpVar))
                _    -> printDescription origVar ipID desc))) $+$
        (printRestriction2 origVar (tmpVar+1) ipID r)
    IRCSomeValuesFrom desc ->
      parens (text "exists" <+> parens (text $ (choiceName tmpVar ++
                                                    " owl:Thing")) <+>
           parens ((text "and") <> parens ((printURIreference ipID) <+>
                  (text ((choiceName origVar)++" "++(choiceName tmpVar)))) <+>
               (case desc of
                DC _ -> parens ((printDescription origVar ipID desc) <+>
                                (text $ choiceName tmpVar))
                _    -> printDescription origVar ipID desc))) $+$
        (printRestriction2 origVar (tmpVar+1) ipID r)
    IRCValue iid ->
      (printURIreference ipID) <+> (text $ choiceName origVar) <+>
          (printURIreference iid) $+$
      (printRestriction2 origVar tmpVar ipID r)
    IRCCardinality cardinality ->
        (printCard origVar ipID cardinality)  $+$
        (printRestriction2 origVar tmpVar ipID r)

instance Pretty Description where
    pretty = printDescription 0 emptyQN

printDescription :: Int -> URIreference -> Description -> Doc
printDescription level iD desc = case desc of
    DC cid -> printURIreference cid
    DR restr -> printRestriction0 level restr
    UnionOf descs ->
      if isEmptyQN iD then
         parens (text "or" <+> (listToDocH (form6 (level+1)) iD descs))
       else
         text "(iff (" <> printURIreference iD <+>
         text (choiceName (level+1) ++ ")") $+$
         text "(or" <+> listToDocH (form6 $ level+1) iD descs
         $+$ text "))"
    IntersectionOf descs ->
      if isEmptyQN iD then
         parens (text "and" <+>
                    listToDocH (form1 $ level+1) iD descs)
       else
         text "(iff (" <> printURIreference iD <+>
         text (choiceName (level+1) ++ ")")
         $+$ text "(and" <+>
         listToDocH (form1 $ level+1) iD descs <> rparen
          $+$ text ")"
    ComplementOf desc1 ->
      if isEmptyQN iD then
         parens (text "not" <+> printDescription (level+1) iD desc1 <+>
                    text (choiceName $ level+1))
       else
         text "(iff (" <> printURIreference iD <+>
         (text $ choiceName $ level+1) <> text ") (not" <+>
         printDescription (level+1) iD desc1 <+>
         (text $ choiceName $ level+1) <> text "))"
    OneOfDes inds ->
      parens (text "or" <> listToDocH (form2 $ level+1) iD inds)

printRestriction0 :: Int -> Restriction -> Doc
printRestriction0 level restr =
    case restr of
      DataRestriction dpID drcom drcoms ->
          printRestriction1 level (level+1) dpID (drcom:drcoms)
      IndivRestriction ipID ircom ircoms ->
          printRestriction2 level (level+1) ipID (ircom:ircoms)

printCard :: Int -> URIreference -> Cardinality -> Doc
printCard level pid card = case card of
    MinCardinality n ->
     if n > 1 then text "exists ((x1 owl:Thing) " <>
        (if n==2 then empty else text "... ") <>
        (text "(x" <> (text $ show  n) <+> text "owl:Thing)) (and " $+$
        brackets (text "ALLDIFFERENT x1 " <>
                     (if n==2 then space else text "... ") <>
                     text "x" <> (text $ show n)) $+$
        parens (printURIreference pid <+> text (choiceName level ++" x1"))
                  <+> (if n==2 then space else text "... ") <>
           parens (printURIreference pid <+> text (choiceName level ++" x") <>
                   (text $ show n)) <> text ")" )
        else
          text "exists (x1 owl:Thing)" <+>
          parens (printURIreference pid <+>
                  text (choiceName level ++" x1"))
    MaxCardinality n ->
     if n > 1 then text "forall ((x1 owl:Thing)" <>
        (if n==2 then space else text "... ") <> text "(x" <>
        (text $ show $ n+1) <+> text "owl:Thing)) (implies" $+$
        text "(" <> printURIreference pid <+>
        text (choiceName level ++ " x1)") <>
        (if n==2 then space else text "... ") <>
        text "(" <> printURIreference pid <+>
        text (choiceName level ++ " x") <> (text $ show $ n+1) <> text "))" $+$
        text "not [ALLDIFFERENT x1" <>
        (if n==2 then space else text "... ") <> text "x" <>
        (text $ show $ n+1) <> text "])"
      else
        text "forall ((x1 owl:Thing))" <+>
        parens (text "implies" $+$
                 parens (printURIreference pid <+>
                          text (choiceName level ++ " x1")))

    Cardinality n ->
     if n > 1 then text "exists ((x1 owl:Thing)" <>
        (if n==2 then space else text "... ") <> text "(x" <> (text $ show n)
        <+> text "owl:Thing)) (and " $+$
        text "[ALLDIFFERENT x1" <>
        (if n==2 then space else text "... ") <> text "x" <> (text $ show n)
        <> text "]" $+$
        text "(" <> printURIreference pid <+>
        text (choiceName level ++ " x1)") <>
        (if n==2 then space else text "... ") <+>
        text "(" <> printURIreference pid <+>
        text (choiceName level ++ " x") <> (text $ show n) <>
        text ")" $+$
        text ("(forall ((" ++ (choiceName $ level+2) ++
                                        " owl:Thing)) (implies") $+$
        text "(" <> printURIreference pid <+>
        text (choiceName level ++" "++ (choiceName $ level+2) ++ ")" ) $+$
        text ("(or (= " ++ (choiceName $ level+2) ++ " x1) ") <>
        (if n==2 then space else text "... ") <>
        text ("(= " ++ choiceName level ++ " " ++ (choiceName $ level+2)) <>
        (text $ show n) <> text "))" $+$
        text "))" $+$ text "))"
      else
        text "exists ((x1 owl:Thing)) (and " $+$
        text "(" <> printURIreference pid <+>
        text (choiceName level ++ " x1)") $+$
        text ("(forall ((" ++ (choiceName $ level+2) ++
                  "owl:Thing)) (implies") $+$
        text "(" <> printURIreference pid <+>
        text (choiceName level ++ " " ++ choiceName (level+2) ++ ")") $+$
        text ("((= " ++ choiceName (level+2) ++ " x1))") $+$
        text "))" $+$
        text ")"

instance Pretty Fact where
    pretty = printFact

printFact :: Fact -> Doc
printFact fact = case fact of
    Indiv individual -> printIndividual individual
    SameIndividual iid1 iid2 iids ->
      listToDocV  (\x y -> parens (text "=" <+> pretty x <+> pretty y))
                        iid1 (iid2:iids)
    DifferentIndividuals iid1 iid2 iids ->
      parens (text "forall ((x owl:Thing))" $+$
              parens (text "or" <+>
                listToDocH (form2 0) emptyQN (iid1:iid2:iids))) $+$
      brackets (text "ALLDEFFERENT" <+>
                listToDocH form3 emptyQN (iid1:iid2:iids))

instance Pretty Individual where
    pretty = printIndividual

printIndividual :: Individual -> Doc
printIndividual (Individual iid _ _ values) =
    printIndividual1 iid values (-1)

printIndividual1 :: (Maybe IndividualID)  -> [Value] -> Int -> Doc
printIndividual1 _ [] _ = empty
printIndividual1 iid' (hv:tv) level = case hv of
    ValueID pid indivID ->
      parens (printURIreference pid <+> pretty iid'
               <+> printURIreference indivID) $+$
      printIndividual1 iid' tv level
    ValueIndiv pid indiv ->
      (if level == -1 then
          printIntIndiv iid' pid indiv 0
        else printIntIndiv iid' pid indiv level)
      $+$ printIndividual1 iid' tv (if level < 0 then 0 else level)
    ValueDL pid dl ->
      parens (printURIreference pid <+> pretty iid' <+> printDataLiteral dl)
      $+$ printIndividual1 iid' tv level

printIntIndiv :: (Maybe IndividualID)
                         -> IndividualvaluedPropertyID
                         -> Individual
                         -> Int
                         -> Doc
printIntIndiv iid' pid ind@(Individual iidI _ typesI valuesI) level =
    case iidI of
      Just _ -> printIndividual ind
      _      -> printAnonymIndividual iid' pid typesI valuesI level

printAnonymIndividual :: (Maybe IndividualID)
                                 -> IndividualvaluedPropertyID
                                 -> [Type]
                                 -> [Value]
                                 -> Int
                                 -> Doc
printAnonymIndividual iid' ipID typesI valuesI level=
    parens (text ("exists (" ++ choiceName level ++ " owl:Thing)")
            $+$ (parens (text "and" <+>
            (parens (printURIreference ipID <+>
               pretty iid' <+> (text $ choiceName level)) $+$
            (listToDocV
               (\x y -> case x of
                   (QN _ str _) ->
                       parens (printDescription 0 emptyQN y <+>
                         text str)) (simpleQN $ choiceName level)
                                   (reverse typesI)) $+$
       printIndividual1 (Just $ simpleQN $ choiceName level)
                         valuesI (level+1)))))

setToDocs :: Pretty a => Set.Set a -> [Doc]
setToDocs = punctuate comma . map pretty . Set.toList

setToDocF :: Pretty a => Set.Set a -> Doc
setToDocF = fsep . setToDocs

setToDocV :: (Pretty a) => Set.Set a -> Doc
setToDocV = vcat . setToDocs

-- output a list in vertikal direction
listToDocV :: (Pretty a, Pretty b)
                  => (a -> b -> Doc) -> a -> [b] -> Doc
listToDocV printForm iD = vcat . map (printForm iD)

-- output a list in horizonal direction
listToDocH :: (Pretty a, Pretty b)
                  =>  (a -> b -> Doc) -> a -> [b] -> Doc
listToDocH printForm iD = hsep . map (printForm iD)

-- output form with different demands
form1 :: Int -> URIreference-> Description -> Doc
form1 level iD des =
   case des of
     DC _ ->
          parens (printDescription level iD des <+> (text $ choiceName level))
     _ -> parens (printDescription level iD des)

form2 :: Int -> URIreference -> IndividualID -> Doc
form2 level _ ind =
    parens (text "=" <+> printURIreference ind <+>
                    (text $ choiceName level))

form3 :: URIreference -> IndividualID -> Doc
form3 _ iid = printURIreference iid

form4 :: URIreference -> DataLiteral -> Doc
form4  _ dl =
    parens (equals <+> printDataLiteral dl <+> text "x")

form5 :: URIreference -> RRange -> Doc
form5 _ dl =
    parens (printRRange dl <+> text "y")

-- only for UnionOf (DEBUG)
form6 :: Int -> URIreference-> Description -> Doc
form6 level iD des =
      parens (printDescription level iD des <+>  (text $ choiceName level))

emptyQN :: QName
emptyQN = QN "" "" ""

simpleQN :: String -> QName
simpleQN str = QN "" str ""

choiceName :: Int -> String
choiceName level
    | level <= 0 = "x"
    | level == 1 = "y"
    | level == 2 = "z"
    | otherwise = "u" ++ (show (level -2))
