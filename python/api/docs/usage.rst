Usage
=====

.. contents::
    :local:

Most of the classes in the library depend on haskell structures and are therefore not ment to be instantiated manually. Rather, the library handles the instantiation. One exception is the :py:class:`~hets.Options` class.

The main entry point is :py:meth:`hets.load_library`. It loads a library from a file path. Once a library is loaded you can perform several actions on the library itself, inspect the development graph with :py:meth:`~hets.Library.development_graph`, and prove or check the consistency of nodes or check the conservativity of an edge.

.. code-block:: python

    import hets

    lib = hets.load_library("Family.dol")
    dg = lib.development_graph()

    nodes = dg.nodes()
    edges = dg.edges()

    print(nodes)
    print(edges)

    [family1, family2] = nodes

    theory1 = family1.global_theory()
    sentences1 = theory1.sentences()
    goals1 = family1.goals()
    axioms1 = family1.axioms()

    goal = goals1[0]
    print(str(goal))
    print(goal.is_proven())

    family1.prove(goals=[goal.name()])

    print(goal.is_proven())


.. code-block:: dol
    :caption: Family.dol

    logic OWL

    ontology Family1 =
      Class: Person
      Class: Woman SubClassOf: Person
      ObjectProperty: hasChild
      Class: Mother
             EquivalentTo: Woman and hasChild some Person
      Individual: mary Types: Woman Facts: hasChild  john
      Individual: john
      Individual: mary
           Types: Annotations: Implied "true"^^xsd:boolean
                  Mother
    end

    ontology Family2 =
      Class: Person
      Class: Woman SubClassOf: Person
      ObjectProperty: hasChild
      Class: Mother
             EquivalentTo: Woman and hasChild some Person
      Individual: mary Types: Woman Facts: hasChild  john
      Individual: john Types: Person
      Individual: mary
           Types: Annotations: Implied "true"^^xsd:boolean Mother
           Types: Annotations: Implied "true"^^xsd:boolean Person
           Types: Annotations: Implied "true"^^xsd:boolean Woman
    end
