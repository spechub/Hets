{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  non-portable(instances for URIreference and Namespace)

Pretty printing for OWL DL theories. 
-}

{-
    todo:
     - invent ASCII display syntax for OWL_DL theories (Klaus)
     - implement printing of a theory
     - shorten lines longer than 80 cpl
-}

module OWL_DL.Print where

import Common.PrettyPrint
import Common.Doc
import Common.DocUtils

import OWL_DL.Sign
import OWL_DL.AS

import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

instance PrintLaTeX Sign where
  printLatex0 = toOldLatex

instance PrettyPrint Sign where
  printText0 = toOldText

instance Pretty Sign where
    pretty = printSign

printSign :: Sign -> Doc
printSign (Sign _ p2 p3 p4 p5 p6 _ p8 p9 p10) =
    (text "namespaces ") $+$ (printNamespace p10) $+$
    ((text "concepts") <+> (printSetWithComma p2)) $+$
    ((text "primaryConcepts ") <+> (printSetWithComma p3)) $+$
    ((text "datatypes ") <+> (printSetWithComma p4)) $+$
    ((text "indvidual_valued_roles ") <+> (printSetWithComma p5)) $+$
    ((text "data_valued_roles ") <+> (printSetWithComma p6)) $+$
    ((text "individuals ") <+> (printSetWithComma p8)) $+$
    ((text "sign_axioms") $+$ (foldSetToDoc2 p9)) $+$ 
    empty

instance PrettyPrint URIreference where
    printText0 = toOldText 

instance Pretty URIreference where
    pretty = printURIreference

printURIreference :: URIreference -> Doc
printURIreference (QN prefix localpart uri)
    | localpart == "_" = text $ show "_"
    | null prefix = if null uri then
                           text localpart
                           else text $ show (uri ++ ":" ++ localpart)
    | otherwise =   text $ show ( prefix ++ ":" ++ localpart)

instance PrettyPrint Namespace where
    printText0 =  toOldText

instance Pretty Namespace where
    pretty = printNamespace

printNamespace :: Namespace -> Doc
printNamespace nsMap =
    vcat $ map pp (Map.toList nsMap)  
       where pp :: (String, String) -> Doc
             pp (s1,s2) = text s1 <> defn <> text s2

instance PrintLaTeX Sentence where
    printLatex0 = toOldLatex

instance PrettyPrint Sentence where
    printText0 = toOldText

instance Pretty Sentence where
    pretty = printSentence

printSentence :: Sentence -> Doc
printSentence sent = case sent of
    OWLAxiom axiom -> printAxiom axiom
    OWLFact fact   -> printFact fact

-- not necessary
instance PrettyPrint Ontology where
    printText0 = toOldText

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

instance PrintLaTeX Ontology where
    printLatex0 = toOldLatex

instance PrettyPrint Directive where
    printText0 = toOldText

instance Pretty Directive where
    pretty = printDirective

printDirective :: Directive -> Doc
printDirective = text . show

instance Pretty Axiom where
    pretty = printAxiom

printAxiom :: Axiom -> Doc
printAxiom axiom = case axiom of
    Class cid _ _ _ descs ->
      foldListToDocV (printDescription (-1)) cid descs 
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
      foldListToDocV  
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
    
instance PrettyPrint Axiom where
    printText0 = toOldText
	      	
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
      foldListToDocH   
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
        foldListToDocH form5 rid rranges $+$ text ")))"
      _         ->
	foldListToDocV   
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

instance PrettyPrint SignAxiom where
    printText0 = toOldText
             
instance PrettyPrint RDomain where
    printText0 = toOldText

instance Pretty RDomain where
    pretty = printRDomain

printRDomain :: RDomain -> Doc
printRDomain (RDomain desc) =
    case desc of
      DC cid -> printURIreference cid <+> text "x"
      _      -> printDescription 0 emptyQN desc  -- ToDo: level hierachie

instance PrettyPrint RRange where
    printText0 = toOldText

instance Pretty RRange where 
    pretty = printRRange

printRRange :: RRange -> Doc
printRRange rRange = case rRange of
    RIRange desc -> printDescription 0 emptyQN desc -- ToDo: level hierachie
    RDRange dataRange -> printDataRange dataRange

instance PrettyPrint DataRange where
    printText0 = toOldText

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
           parens (foldListToDocH form4 emptyQN dls)) <>
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

instance PrettyPrint DataLiteral where
    printText0 = toOldText

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
instance PrettyPrint Restriction where
    printText0 = toOldText

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
   

instance PrettyPrint Description where
    printText0 = toOldText

instance Pretty Description where
    pretty = printDescription 0 emptyQN

printDescription :: Int -> URIreference -> Description -> Doc
printDescription level iD desc = case desc of
    DC cid -> printURIreference cid
    DR restr -> printRestriction0 level restr
    UnionOf descs ->
      if isEmptyQN iD then
         parens (text "or" <+> (foldListToDocH (form6 (level+1)) iD descs))
       else
         text "(iff (" <> printURIreference iD <+> 
         text (choiceName (level+1) ++ ")") $+$
         text "(or" <+> foldListToDocH (form6 $ level+1) iD descs
         $+$ text "))"
    IntersectionOf descs -> 
      if isEmptyQN iD then
         parens (text "and" <+> 
                    foldListToDocH (form1 $ level+1) iD descs)
       else
         text "(iff (" <> printURIreference iD <+> 
         text (choiceName (level+1) ++ ")")
         $+$ text "(and" <+> 
         foldListToDocH (form1 $ level+1) iD descs <> rparen 
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
      parens (text "or" <> foldListToDocH (form2 $ level+1) iD inds) 
      
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

instance PrettyPrint Fact where
    printText0 = toOldText

instance Pretty Fact where
    pretty = printFact

printFact :: Fact -> Doc
printFact fact = case fact of
    Indiv individual -> printIndividual individual
    SameIndividual iid1 iid2 iids -> 
      foldListToDocV  (\x y -> parens (text "=" <+> pretty x <+> pretty y))
                        iid1 (iid2:iids)
    DifferentIndividuals iid1 iid2 iids -> 
      parens (text "forall ((x owl:Thing))" $+$
              parens (text "or" <+> 
                foldListToDocH (form2 0) emptyQN (iid1:iid2:iids))) $+$
      brackets (text "ALLDEFFERENT" <+> 
                foldListToDocH form3 emptyQN (iid1:iid2:iids))

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
            (foldListToDocV  
               (\x y -> case x of 
                   (QN _ str _) -> 
                       parens (printDescription 0 emptyQN y <+> 
                         text str)) (simpleQN $ choiceName level) 
                                   (reverse typesI)) $+$
       printIndividual1 (Just $ simpleQN $ choiceName level) 
                         valuesI (level+1)))))

instance PrettyPrint Individual where
   printText0 = toOldText
           
foldSetToDoc2 :: (Pretty a) => Set.Set a -> Doc
foldSetToDoc2 = vcat . punctuate comma . map pretty . Set.toList

-- output a list in vertikal direction
foldListToDocV :: (Pretty a, Pretty b) 
                  => (a -> b -> Doc) -> a -> [b] -> Doc
foldListToDocV printForm iD = vcat . map (printForm iD) 

-- output a list in horizonal direction
foldListToDocH :: (Pretty a, Pretty b) 
                  =>  (a -> b -> Doc) -> a -> [b] -> Doc
foldListToDocH printForm iD = hsep . map (printForm iD) 

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
