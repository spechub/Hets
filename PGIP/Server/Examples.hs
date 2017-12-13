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
      \  (forall (x y z) (if (and (isProperPartOf x y) (isProperPartOf y z))\n\
      \                      (isProperPartOf x z)))\n\
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

propositional :: String
propositional = "logic Propositional\n\
                \spec Raining =\n\
                \  props raining, wet_street\n\
                \  . raining => wet_street\n\
                \                    %(if raining, the street is wet)%\n\
                \end\n\
                \spec Scenario1 = Raining then\n\
                \  . not wet_street    %(the street is not wet)%\n\
                \  . not raining       %(it is not raining)%  %implied\n\
                \end\n\
                \spec Scenario2 = Raining then\n\
                \  . wet_street      %(the street is wet)%\n\
                \  %% the following does not hold...\n\
                \  . raining         %(hence it must rain...)%  %implied\n\
                \end"

rdf :: String
rdf = "@prefix rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#> .\n\
      \@prefix dc: <http://purl.org/dc/elements/1.1/> .\n\
      \@prefix ex: <http://example.org/stuff/1.0/> .\n\
      \\n\
      \<http://www.w3.org/TR/rdf-syntax-grammar>\n\
      \  dc:title \"RDF/XML Syntax Specification (Revised)\" ;\n\
      \  ex:editor [\n\
      \    ex:fullname \"Dave Beckett\";\n\
      \    ex:homePage <http://purl.org/net/dajobe/>\n\
      \  ] ."

tptp :: String
tptp = "fof(irreflexive, axiom,\n\
       \ ! [X]: (~ less(X, X))).\n\
       \fof(transitive, axiom,\n\
       \ ! [X, Y, Z]: ((less(X, Y) & less(Y, Z)) => less(X, Z))).\n\
       \fof(asYmmetric, conjecture,\n\
       \ ! [X, Y]: (less(X, Y) => ~ less(Y, X)))."

hascasl :: String
hascasl = "logic HasCASL\n\
          \spec Functions =\n\
          \  ops __o__ : forall a, b, c:Type . \n\
          \               (b ->? c) * (a ->? b) -> (a ->? c);\n\
          \      id    : forall a:Type . a ->? a;\n\
          \  vars a, b, c : Type;\n\
          \         g         : b ->? c;\n\
          \         f         : a ->? b;\n\
          \         x         : a\n\
          \   . g o f = \\ x . g (f x)               %(o_def)%\n\
          \   . id = \\ x . x                        %(id_def)%\n\
          \ then %implies\n\
          \  vars a, b, c , d : Type;\n\
          \         f'         : a ->? a;\n\
          \         h          : c ->? d;\n\
          \         g          : b ->? c;\n\
          \         f          : a ->? b\n\
          \   . h o (g o f) = (h o g) o f           %(o_assoc)%\n\
          \   . f' o id = f'                        %(id_neut)%\n\
          \   . f' o f' = id => forall x, y:a .\n\
          \         f' x = f' y => x = y            %(inj)%\n\
          \   . f' o f' = id => forall x:a .\n\
          \         exists y:a . f' y = x           %(surj)%\n\
          \end"

modal :: String
modal = "logic Modal\n\
        \spec M =\n\
        \     modality empty { [](p /\\ q) => []p }\n\
        \end\n\
        \spec K =\n\
        \     modality empty { [] true; [](p => q) => ([]p => []q) }\n\
        \end\n\
        \spec T = K then\n\
        \     modality empty { []p => p }\n\
        \end\n\
        \spec S4 = T then\n\
        \     modality empty { []A => [][]A }\n\
        \end\n\
        \spec S5 = T then\n\
        \     modality empty {<>A => []<>A}\n\
        \end"

