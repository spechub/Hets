{- |
Module      :  $Header$
Copyright   :  (c) Heng Jiang, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  portable

Pretty printing for OWL DL theories. 

-}

{-
    todo:
     - invent ASCII display syntax for OWL_DL theories (Klaus)
     - implement printing of a theory
     - shorten lines longer than 80 cpl
-}

module OWL_DL.Print where

import Common.GlobalAnnotations
import Common.Lib.Pretty
import Common.PrettyPrint

import Text.XML.HXT.DOM.XmlTreeTypes 
import OWL_DL.Sign
import OWL_DL.AS

import qualified Common.Lib.Set as Set
import qualified Common.Lib.Map as Map

instance PrintLaTeX Sign where
  printLatex0 = printText0

instance PrettyPrint Sign where
  printText0 ga (Sign _ p2 p3 p4 p5 p6 _ p8 p9 p10) =
    (text "namespaces ") $+$ (printText0 ga p10) $+$
    ((text "concepts ") <> (foldSetToDoc ga p2)) $+$
    ((text "primaryConcepts ") <> (foldSetToDoc ga p3)) $+$
    ((text "datatypes ") <> (foldSetToDoc ga p4)) $+$
    ((text "indvidual_valued_roles ") 
                         <> (foldSetToDoc ga p5)) $+$
    ((text "data_valued_roles ") <> (foldSetToDoc ga p6)) $+$
    ((text "individuals ") <> (foldSetToDoc ga p8)) $+$
    ((text "sign_axioms") $+$ (foldSetToDoc2 ga p9)) $+$ 
    empty

instance PrettyPrint URIreference where
    printText0 _ (QN prefix localpart uri)
        | localpart == "_" = text $ show "_"
        | null prefix = if null uri then
                           text localpart
                           else text $ show (uri ++ ":" ++ localpart)
        | otherwise =   text $ show ( prefix ++ ":" ++ localpart) 

instance PrettyPrint Namespace where
    printText0 _ nsMap = 
        text $ pp (Map.toList nsMap) "" 
       where pp :: [(String, String)] -> String ->  String
             pp [] str = str ++ "\n"
             pp ((pre, uri):rest) str 
                 | null str = pp rest (pre ++ " ::= " ++ uri)
                 | otherwise =         
                     pp rest (str ++ "\n" ++ pre ++ " ::= " ++ uri) 
           
instance PrintLaTeX Sentence where
  printLatex0 = printText0

instance PrettyPrint Sentence where
    printText0 ga sent = 
        case sent of
          OWLAxiom axiom -> printText0 ga axiom
          OWLFact fact   -> printText0 ga fact

-- not necessary
instance PrettyPrint Ontology where
    printText0 ga (Ontology maybeID directives ns) =
        (text "Ontology") <+> 
            (case maybeID of
             Just oid -> printText0 ga oid
             _        -> text "anomie"
            ) $+$
        (text $ show $ map (printText0 ga) directives) $+$
        (printText0 ga ns)

instance PrintLaTeX Ontology where
 printLatex0 = printText0

instance PrettyPrint Directive where
    printText0 _ = text . show

instance PrettyPrint Axiom where
    printText0 ga axiom =
	case axiom of
	Class cid _ _ _ descs ->       -- descs is here unionOf or complementOf
          foldListToDocV ga (printDescription ga 0) cid descs
	EnumeratedClass cid _ _ iids ->
                  parens ((text "forall ((x owl:Thing))") $+$ 
	                  (printDescription ga 0 cid $ OneOfDes iids)) 
	DisjointClasses desc1 desc2 _ ->   -- description list is ignored (always empty)
	   parens ((text "forall ((x owl:Thing))") <+>
                    parens ((text "not") <+> parens ((text "and") <+>
                    parens ((printDescription ga 0 emptyQN desc1) <+>
                     (text "x")) <+> 
                     parens ((printDescription ga 0 emptyQN desc2) <+> (text "x")))))

	EquivalentClasses desc1 descs ->  
         foldListToDocV ga 
	  (\x y -> 
          case y of
	  DC cid2 ->
	    parens ((text "forall ((x owl:Thing))") <+> 
                    parens (text "iff" <> 
                    parens ((printDescription ga 0 emptyQN x) <+> 
                    (text "x")) <+> parens ((printText0 ga cid2) <+> 
                    (text "x"))))	
	  _      -> 
	      case x of
	        DC cid1 ->
                   parens ((text "forall ((x owl:Thing))") $+$ 
                            (printDescription ga 0 cid1 y))
	        _       -> error ("EquivalentClasses Error:" ++ (show axiom))
	  ) desc1 descs
	Datatype dID _ _ -> 
	    printText0 ga dID
	DEquivalentProperties dpID1 dpID2 _ ->
	    parens ((text "forall ((x owl:Thing) (y owl:Thing))") <+> 
                     parens ((text "iff") <> parens ((printText0 ga dpID1) <+>
                     (text "x y")) <+> parens ((printText0 ga dpID2) <+>
			                       (text "x y"))))	
	IEquivalentProperties ipID1 ipID2 _ ->
	    parens ((text "forall ((x owl:Thing) (y owl:Thing))") <+> 
                    parens ((text "iff") <> parens ((printText0 ga ipID1) <+>
			(text "x y")) <+> parens ((printText0 ga ipID2) <+>
			(text "x y"))))	

	DSubPropertyOf dpID1 dpID2 ->
	    parens ((text "forall ((u owl:Thing) (y rdfs:Lilteral))") <+> 
                    parens ((text "implies") <> 
                            parens ((printText0 ga dpID1) <+>
			            (text "u y")) <+> 
                            parens ((printText0 ga dpID2) <+>
			            (text "u y"))))	
	ISubPropertyOf ipID1 ipID2 ->
	    parens ((text "forall ((u owl:Thing) (y owl:Thing))") <+> 
                    parens ((text "implies") <> 
                            parens ((printText0 ga ipID1) <+>
			            (text "u y")) <+> 
                            parens ((printText0 ga ipID2) <+>
			            (text "u y"))))
	ObjectProperty iid p2 p3 p4 maybeInverse isSymmetric maybeFunc p8 p9 ->
	    case maybeInverse of
	    Just pid -> parens ((text "forall ((x owl:Thing) (y owl:Thing))") 
                                <+>  parens ((text "iff") <> 
                                             parens ((printText0 ga iid) <+>
			                             (text "x y")) <+> 
                                             parens ((printText0 ga pid) <+>
			                             (text "y x"))))  
               -- inverse and transitive properties are separated. 
  	       -- 	(printText0 ga (ObjectProperty iid p2 p3 p4 
               --         Prelude.Nothing isSymmetric maybeFunc p8 p9))
	    _ -> if isSymmetric then
                     parens ((text "forall ((x owl:Thing) (y owl:Thing))") 
                                <+>  parens ((text "implies") <> 
                                             parens ((printText0 ga iid) <+>
			                             (text "x y")) <+> 
                                             parens ((printText0 ga iid) <+>
			                             (text "y x"))))  
		    else 
		      case maybeFunc of
		         Just InverseFunctional ->
                           parens ((text "forall ((x owl:Thing) (y owl:Thing) (z owl:Thing))") <+>  
                             parens ((text "implies") $+$ 
                                     (nest 2 (parens ((text "and") <> 
                                              parens ((printText0 ga iid) <+>
			                             (text "y z")) $+$ 
                                               parens ((printText0 ga iid) <+>
			                             (text "z x"))))) $+$
                                     (nest 2 $ parens (text "= y z"))))
                         Just Transitive ->  
                           parens ((text "forall ((x owl:Thing) (y owl:Thing) (z owl:Thing))") <+>  
                             parens ((text "implies") $+$ 
                                     (nest 2 (parens ((text "and") <> 
                                              parens ((printText0 ga iid) <+>
			                             (text "x y")) $+$ 
                                               parens ((printText0 ga iid) <+>
			                             (text "y z"))))) $+$
                                     (nest 2 $ parens (text "x z"))))
			 _  -> text "" 
	u -> text $ show u         -- annotation is not yet instanced

instance PrettyPrint SignAxiom where
    printText0 ga signAxiom =
	case signAxiom of
	Subconcept cid1 cid2 -> 
	    (text "(forall ((u owl:Thing)) (implies (" <> 
	             (printText0 ga cid1) <> 
	             (text " u) (") <> (printText0 ga cid2) <> (text " u)))"))
	RoleDomain rid rdomains ->
	    foldListToDocH ga  
	    (\x y -> parens ((text "forall ((u owl:Thing) (y owl:Thing))") $+$
                             (nest 2 $ parens ((text "implies (") <> 
                                               (parens ((printText0 ga x) <+> 
                                                        (text "u y)") <+> 
                                                        (parens (printText0 ga y)))))))
            ) rid rdomains
	RoleRange rid rranges -> 
 --        if null rranges then text ""
 --          else
            case head rranges of
	    RDRange _ ->          -- range (dataRange) of datatype property
	     (text "(forall ((x owl:Thing) (y rdfs:Literal))") $+$
                (nest 2 $ text "(implies (") <> (printText0 ga rid) <+>
		(text "x y)") $+$
                (if (length rranges > 1) then
		    (nest 4 $ text "(or ") 
                   else (nest 4 $ lparen))
		<> (foldListToDocH ga (form5 ga) rid rranges)
                $+$ (text ")))")
	    _         ->
	      foldListToDocV ga  
	        (\x y -> (text "(forall ((u owl:Thing) (y owl:Thing))")
                     $+$ (nest 2 $ text "(implies (") <> (printText0 ga x) <+> 
	             (text "u y) (") <> (printText0 ga y) <> (text " y)") $+$
	             (text "))"))
	           rid rranges
	FuncRole (rtype, rid) ->
	    case rtype of
	    IRole -> 
		(text "(forall ((x owl:Thing) (y owl:Thing) (z owl:Thing))")
	        $+$ (nest 2 $ text "(implies") $+$
	        ((nest 4 $ text "(and (") <> (printText0 ga rid) <+> 
	        (text "x y) (") <+> (printText0 ga rid) <+> (text "x z))")) $+$
	        (nest 4 $ text "(= y z)") $+$
	        (text "))") 
	    DRole ->
	     (text "(forall ((x owl:Thing) (y rdfs:Literal) (z rdfs:Literal))")
	      $+$ (nest 2 $ text "(implies") $+$
	      ((nest 4 $ text "(and (") <> (printText0 ga rid) <+> 
	      (text "x y) (") <+> (printText0 ga rid) <+> (text "x z))")) $+$
	      (nest 4 $ text "(= y z)") $+$
	      (text "))")
	Conceptmembership iID desc ->
	    parens ((printDescription ga 0 iID desc) 
		     <+> (printText0 ga iID))

instance PrettyPrint RDomain where
    printText0 ga (RDomain desc) =
      case desc of
        DC cid -> printText0 ga cid <+> (text "u")
        _      -> printDescription ga 0 emptyQN desc   -- ToDo: level hierachie

instance PrettyPrint RRange where
    printText0 ga rRange =
        case rRange of
        RIRange desc -> printDescription ga 0 emptyQN desc -- ToDo: level hierachie
        RDRange dataRange -> printText0 ga dataRange 

instance PrettyPrint DataRange where
    printText0 ga dr =
      case dr of
        DID dtID -> printText0 ga dtID
        OneOfData dls ->
         parens ((text "forall ((x rdfs:Literal))") $+$
             (if allEqTypedLit dls then
                 case head dls of
                 TypedL (_, drType) ->
                    (nest 2 $ text "(iff (") <> (printText0 ga drType) <+> 
                    (text "x)") 
                 _  -> error "false check datarange."
                else empty) $+$ 
              (nest 3 $ parens (text "or") <> 
               parens (foldListToDocH ga (form4 ga) emptyQN dls)) <> 
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
    printText0 ga dl =
        case dl of
        TypedL (lf, uri) -> parens (text (lf ++ ":") <+> 
                                     printText0 ga uri)
        PlainL (lf, lt)  -> parens (text ("stringInLang '"++lf++" : "++lt))
        Plain lf         -> text lf 
        RDFSL rdfLit     -> -- (text "rdf_literal") <+> (text rdfLit)
                            text rdfLit

instance PrettyPrint Restriction where
    printText0 ga restr =
        case restr of
        DataRestriction dpID drcom drcoms ->
            printRestriction1 ga dpID (drcom:drcoms)
        IndivRestriction ipID ircom ircoms ->
            printRestriction2 ga ipID (ircom:ircoms)

instance PrettyPrint Description where
    printText0 ga desc =
        printDescription ga 0 emptyQN desc -- ToDo: level hierachie

instance PrettyPrint Fact where
    printText0 ga fact =
        case fact of
        SameIndividual iid1 iid2 iids -> 
            foldListToDocV ga (\x y -> parens ((text "=") <+> (printText0 ga x)
                               <+> (printText0 ga y)))
                           iid1 (iid2:iids)
        DifferentIndividuals iid1 iid2 iids -> 
            (text "(forall ((x owl:Thing))") $+$
              (nest 2 $ text "(or (") <> 
              (foldListToDocH ga (form2 ga) emptyQN (iid1:iid2:iids)) <> 
              (text ")))") $+$
              (text "[ALLDIFFERENT") <+> 
              (foldListToDocH ga (form3 ga) emptyQN (iid1:iid2:iids)) <> 
              (char ']')
        Indiv individual -> printText0 ga individual

instance PrettyPrint Individual where
   printText0 ga (Individual iid _ _ values) =
       printIndividual iid values (-1)

     where printIndividual :: (Maybe IndividualID) 
                           -> [Value]
                           -> Int 
                           -> Doc
           printIndividual _ [] _ = empty
           printIndividual iid' (hv:tv) level =
               case hv of
               ValueID pid indivID -> 
                   parens ((printText0 ga pid) <+> (printText0 ga iid')
                   <+> (printText0 ga indivID)) $+$
                   (printIndividual iid' tv level)
               ValueIndiv pid indiv ->
                 (if level == -1 then
                     parens ((printText0 ga pid) <+> (printText0 ga iid')
                             $+$ (nest 2 $ printIntIndiv iid' pid indiv 0))
                     else (printIntIndiv iid' pid indiv level))
                   $+$ (nest 2 $ printIndividual iid' tv 
                        (if level < 0 then 0 else level))
               ValueDL pid dl ->
                   parens ((printText0 ga pid) <+> (printText0 ga iid')
                           <+> (printText0 ga dl)) $+$
                   (printIndividual iid' tv level)
           
           printIntIndiv :: (Maybe IndividualID)
                         -> IndividualvaluedPropertyID 
                         -> Individual
                         -> Int
                         -> Doc
           printIntIndiv iid' pid ind@(Individual iidI _ typesI valuesI) level
             = case iidI of
               Just _ -> printText0 ga ind
               _      -> printAnonymIndividual iid' pid typesI valuesI level
                         
           printAnonymIndividual :: (Maybe IndividualID)
                                 -> IndividualvaluedPropertyID
                                 -> [Type]
                                 -> [Value]
                                 -> Int
                                 -> Doc
           printAnonymIndividual iid' ipID typesI valuesI level= 
               parens ((text ("exists (" ++ choiceName level ++ ")")) $+$ 
                 (nest 2 $ parens ((text "and") <+> 
                  (foldListToDocH ga 
                   (\x y -> case x of 
                       (QN _ str _) -> 
                        parens ((printDescription ga 0 emptyQN y) <+> 
                         (text str))) (simpleQN $ choiceName level) typesI) $+$
                   (nest 4 $ parens ((printText0 ga ipID) <+> 
                      (printText0 ga iid') <+> (text $ choiceName level))) $+$ 
                  (nest 4 $ printIndividual (Just $ simpleQN $ choiceName level) valuesI (level+1)))))
           
       
-- to show restrictions, descriptions and cardinalities need the id of classes
-- or properties, so those are implemented not in PrettyPrint. 
printRestriction1 :: GlobalAnnos -> URIreference -> [Drcomponent] -> Doc
printRestriction1 _ _ [] = empty
printRestriction1 ga dpID (h:r) =
    case h of
    DRCAllValuesFrom dataRange -> 
	-- (text "(forall ((x owl:Thing)) ") $+$
	-- (nest 2 $ text "(restriction x)") $+$
	parens ((text "forall (y rdfs:Literal)") <+> 
                parens ((text "implies") <> parens ((printText0 ga dpID) <+>
	                                            (text "x y")) <+> 
                        parens ((printText0 ga dataRange) <+> (text "y")))) $+$
	-- (text ")") $+$
	(printRestriction1 ga dpID r)
    DRCSomeValuesFrom dataRange -> 
	-- (text "(forall ((x owl:Thing)) ") $+$
	-- (nest 2 $ text "(restriction x)") $+$
	parens ((text "exists (y rdfs:Literal)") <+> 
                parens ((text "and") <> parens ((printText0 ga dpID) <+>
	                                        (text "x y")) <+> 
                        parens ((printText0 ga dataRange) <+> (text "y")))) $+$
	-- (text ")") $+$
	(printRestriction1 ga dpID r)
    DRCValue dl -> 
	-- (text "(forall ((x owl:Thing)) (") <>
	  (printText0 ga dpID) <+> (text "x") <+>
	  (printText0 ga dl) $+$
	(printRestriction1 ga dpID r)
    DRCCardinality cardinality -> 
        (printCard ga dpID cardinality) $+$
        (printRestriction1 ga dpID r)

printRestriction2 :: GlobalAnnos -> URIreference -> [Ircomponent] -> Doc
printRestriction2 _ _ [] = empty
printRestriction2 ga ipID (h:r) =
    case h of
    IRCAllValuesFrom desc -> 
	-- (text "(forall ((x owl:Thing)) ") $+$
	-- (nest 2 $ text "(restriction x)") $+$
	parens ((text "forall ((y owl:Thing))") <+> 
                parens ((text "implies") <+> parens ((printText0 ga ipID) <+>
	                                            (text "x y")) <+> 
                        parens ((printDescription ga 0 ipID desc) <+> 
                                (text "y")))) $+$
	-- (text ")") $+$
	(printRestriction2 ga ipID r)
    IRCSomeValuesFrom desc -> 
	-- (text "(forall ((x owl:Thing)) ") $+$
	-- (nest 2 $ text "(restriction x)") $+$
	parens ((text "exists (y owl:Thing)") <+> 
                parens ((text "and") <> parens ((printText0 ga ipID) <+>
	                                            (text "x y")) <+> 
                        parens ((printDescription ga 0 ipID desc) <+> 
                                (text "y")))) $+$
	-- (text ")") $+$
	(printRestriction2 ga ipID r)
    IRCValue iid -> 
	-- (text "(forall ((x owl:Thing)) (") <>
	  (printText0 ga ipID) <+> (text "x") <+>
	  (printText0 ga iid) $+$
	(printRestriction2 ga ipID r)

    IRCCardinality cardinality -> 
        (printCard ga ipID cardinality)  $+$
        (printRestriction2 ga ipID r)

printCard :: GlobalAnnos -> URIreference -> Cardinality -> Doc
printCard ga pid card =
    case card of
    MinCardinality n -> 
     if n > 1 then
      parens (-- (text "forall ((x owl:Thing)) ") $+$
	-- (nest 2 $ text "(restriction x)") $+$
	( parens  
         ((text "exists ((x1 owl:Thing) ... (x") <> (int n) <+>
                                  (text "owl:Thing)) (and ") $+$
        (nest 2 $ brackets ((text "ALLDIFFERENT x1 ... x") <> (int n))) $+$ 
        (nest 2 $ text "(") <> (printText0 ga pid) <+> (text "x x1) ...") <+>
	   (text "(") <> (printText0 ga pid) <+> (text "x x") <> (int n) <>
			          (text "))")
	 )))
      else
       parens (-- (text "forall ((x owl:Thing)) ") $+$
	       (parens 
                ((text "exists (x1 owl:Thing)") <+>
                 (parens ((printText0 ga pid) <+> (text "x x1"))))))
    MaxCardinality n -> 
     if n > 1 then
      parens ((text "forall ((x1 owl:Thing) ... (x") <> 
              (int (n+1)) <+> (text "owl:Thing)) (implies") $+$
	      -- (nest 2 $ text "(and (restriction x)") $+$
	      (nest 3 $ text "(") <> (printText0 ga pid) <+> 
              (text "x x1) ...")<+> (text "(") <> (printText0 ga pid) <+> 
              (text "x x") <> (int (n+1)) <> (text "))") $+$
	      (nest 2 $ (text "not [ALLDIFFERENT x1 ... x")) <> (int (n+1)) <>
              (text "])"))
      else 
        parens ((text "forall ((x1 owl:Thing))") <+> 
                (parens ((text "implies") $+$
		         (nest 2 $ parens ((printText0 ga pid) <+> 
                                           (text "x x1"))))))
    Cardinality n ->
     if n > 1 then
      -- (text "(forall ((x owl:Thing)) ") $+$
	-- (nest 2 $ text "(restriction x)") $+$
	(text "(exists ((x1 owl:Thing) ... (x") <> (int n) <+>
                                  (text "owl:Thing)) (and ") $+$
        (nest 2 $ text "[ALLDIFFERENT x1 ... x") <> (int n) <>
                                  (text "]") $+$
	(nest 2 $ text "(") <> (printText0 ga pid) <+> (text "x x1) ...") <+>
	   (text "(") <> (printText0 ga pid) <+> (text "x x") <> (int n) <>
			          (text ")") $+$
	(nest 2 $ text "(forall ((z owl:Thing)) (implies") $+$
	(nest 4 $ text "(") <> (printText0 ga pid) <+> (text "x z)") $+$
	(nest 4 $ text "(or (= z x1) ... (= z x") <> (int n) <> 
	           (text "))") $+$
	(nest 2 $ text "))") $+$
	(text ")))") 
       else 
        -- (text "(forall ((x owl:Thing)) ") $+$
	(text "(exists ((x1 owl:Thing)) (and ") $+$
        (nest 2 $ text "(") <> (printText0 ga pid) <+> (text "x x1)") $+$
	(nest 2 $ text "(forall ((z owl:Thing)) (implies") $+$
	(nest 4 $ text "(") <> (printText0 ga pid) <+> (text "x z)") $+$
	(nest 4 $ text "((= z x1))") $+$
	(nest 2 $ text "))") $+$
	(text ")))")

printDescription :: GlobalAnnos -> Int -> URIreference -> Description -> Doc
printDescription ga level iD desc =
    case desc of
        DC cid -> printText0 ga cid
        DR restr -> printText0 ga restr
        UnionOf descs -> 
         if isEmptyQN iD then
            parens ((text "or (") <> (foldListToDocH ga (form6 ga level) iD descs)
                                        <> (char ')')) 
           else
            -- (text "(forall ((x owl:Thing))") $+$
            (text "(iff (") <> (printText0 ga iD) <+> 
                                (text (choiceName level ++ ")")) $+$
            (nest 2 $ text "(or (") <> (foldListToDocH ga (form6 ga level) iD descs)
                                        $+$ -- <> (char ')') $+$
            (text ")))") 
        IntersectionOf descs -> 
         if isEmptyQN iD then
            parens ((text "and (") <> 
                    (foldListToDocH ga (form1 ga level) iD descs) <> (char ')')) 
           else
            -- (text "(forall ((x owl:Thing))") $+$
              (text "(iff (") <> (printText0 ga iD) <+> (text (choiceName level ++ ")"))
              $+$ (nest 2 $ text "(and (") <> 
              (foldListToDocH ga (form1 ga level) iD descs) <> (char ')')  $+$
              (text ")))")
        ComplementOf desc1 ->
         if isEmptyQN iD then
            parens ((text "not (") <> (printDescription ga (level +1) iD desc1) <+>
                    (text (choiceName level ++ ")")))
           else
            (text "(iff (") <> (printText0 ga iD) <+>
                    ((text $ choiceName level) <> (text ") (not (")) <> (printDescription ga (level+1) iD desc1) <+>
                    ((text $ choiceName level) <> (text ")))"))
        OneOfDes inds -> 
         if isEmptyQN iD then
            parens ((text "or (") <> (foldListToDocH ga (form2 ga) iD inds) 
                                        <> (char ')'))             
           else
            -- (text "(forall ((x owl:Thing)) ") $+$
            (text "(iff (") <> (printText0 ga iD) <+> ((text $ choiceName level) <> (text ")")) $+$
            (nest 2 $ text "(or (") <> (foldListToDocH ga (form2 ga) iD inds) 
                                        $+$ -- <> (char ')') $+$
            (text ")))") 

-- form of pretty print 
foldSetToDoc :: (PrettyPrint a) => GlobalAnnos -> Set.Set a -> Doc
foldSetToDoc ga idSet =
    foldr addDoc empty $ map (printText0 ga) (Set.toList idSet)
   where addDoc :: Doc -> Doc -> Doc
         addDoc d1 d2
             | isEmpty d2 = d1
             | otherwise = d1 <> (text ", ") <> d2

foldSetToDoc2 :: (PrettyPrint a) => GlobalAnnos -> Set.Set a -> Doc
foldSetToDoc2 ga idSet =
    foldr addDoc empty $ map (printText0 ga) (Set.toList idSet)
   where addDoc :: Doc -> Doc -> Doc
         addDoc d1 d2
             | (isEmpty d1) && (isEmpty d2) = empty     
             | isEmpty d1 = d2  
             | isEmpty d2 = d1
             | otherwise = d1 <> (char ',') $+$ d2

-- output a list in vertikal direction
foldListToDocV :: (PrettyPrint a, PrettyPrint b) 
                 => GlobalAnnos -> (a -> b -> Doc) -> a -> [b] -> Doc
foldListToDocV _ _ _ [] = empty
foldListToDocV ga printForm iD (h:r) =
    (printForm iD h) $+$ (foldListToDocV ga printForm iD r) 

-- output a list in horizonal direction
foldListToDocH :: (PrettyPrint a, PrettyPrint b) 
                 => GlobalAnnos -> (a -> b -> Doc) -> a -> [b] -> Doc
foldListToDocH _ _ _ [] = empty
foldListToDocH ga printForm iD (h:r) =
    (printForm iD h) <+> (foldListToDocH ga printForm iD r)

-- output form with different demands
form1 :: GlobalAnnos -> Int -> URIreference-> Description -> Doc
form1 ga level iD des =
          parens (printDescription ga level iD des)  
      --           <+>  (text "x)")      -- should x be deleted?

form2 :: GlobalAnnos -> URIreference -> IndividualID -> Doc
form2 ga _ ind = 
    parens ((text "=") <+> (printText0 ga ind) <+> 
                    (text "x"))

form3 :: GlobalAnnos -> URIreference -> IndividualID -> Doc
form3 ga _ iid =  printText0 ga iid

form4 :: GlobalAnnos -> URIreference -> DataLiteral -> Doc
form4 ga _ dl = 
    parens ((text "=") <+> (printText0 ga dl) <+> 
                    (text "x"))

form5 :: GlobalAnnos -> URIreference -> RRange -> Doc
form5 ga _ dl = 
    parens ((printText0 ga dl) <+> (text "y"))

-- only for domain (DEBUG)
form6 :: GlobalAnnos -> Int -> URIreference-> Description -> Doc
form6 ga level iD des =
          parens ((printDescription ga level iD des) <+>  (text "u"))

emptyQN :: QName
emptyQN = QN "" "" ""

simpleQN :: String -> QName
simpleQN str = QN "" str ""
               
choiceName :: Int -> String
choiceName level 
    | level == 0 = "x"
    | level == 1 = "y"
    | level == 2 = "z"
    | otherwise = "z" ++ (show (level -2))
