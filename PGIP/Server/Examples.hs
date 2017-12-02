module PGIP.Server.Examples where

dol :: String
dol = "%% a simple parthood ontology in OWL\n\
      \logic OWL\n\
      \ontology Parthood_OWL =\n\
      \  ObjectProperty: isPartOf\n\
      \  ObjectProperty: isProperPartOf\n\
      \  Characteristics: Asymmetric\n\
      \  SubPropertyOf: isPartOf\n\
      \end\n\
      \\n\
      \%% we cannot specify an object property to be both asymmetric and transitive in OWL. Therefore, we switch to Common Logic\n\
      \logic CommonLogic\n\
      \ontology Parthood_CL =\n\
      \  Parthood_OWL\n\
      \  with translation OWL22CommonLogic\n\
      \then\n\
      \  (if (and (isProperPartOf x y) (isProperPartOf y z))\n\
      \      (isProperPartOf x z))\n\
      \end"

casl :: String
casl = "spec Strict_Partial_Order =\n\
       \sort Elem\n\
       \pred __<__ : Elem * Elem\n\
       \forall x, y, z:Elem\n\
       \. not x < x %(irreflexive)%\n\
       \. x < y /\\ y < z => x < z %(transitive)%\n\
       \%% the following is logically entailed\n\
       \. x < y => not y < x %(asymmetric)% %implied\n\
       \end"

owl :: String
owl = "Prefix: : <http://example.org/>\n\
      \Ontology: <http://example.org/Family>\n\
      \AnnotationProperty: Implied\n\
      \Class: Person\n\
      \Class: Woman SubClassOf: Person\n\
      \ObjectProperty: hasChild\n\
      \Class: Mother \n\
       \      EquivalentTo: Woman and hasChild some Person\n\
      \Individual: mary Types: Woman Facts: hasChild  john\n\
      \Individual: john Types: Person\n\
      \Individual: mary \n\
      \     Types: Annotations: Implied \"true\"^^xsd:boolean\n\
      \            Mother"

clif :: String
clif = "(cl-text strict_partial_order.clif\n\
       \  (forall (x) (not (< x x))) // irreflexive\n\
       \  (forall (x y z) (if (and (< x y) (< y z)) (< x z))) // transitive\n\
       \  (forall (x y) (if (< x y) (not (< y x)))) // asymmetric\n\
       \)"
