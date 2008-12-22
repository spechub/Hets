{- |
Description : infrastructure needed for presenting a logic to Hets

The folder "Logic" contains the infrastructure needed for
presenting a logic to Hets. A logic here is understood in
the theory of institutions. More precisely, a logic is
an entailment system in the sense of Meseguer.
An entailment system consists of a category
of signatures and signature morphisms, a set of sentences
for each signature, a sentence translation map of each
signature morphism, and an entailment relation
between sets of sentences and sentences for each signature.

The module "Logic.Logic" contains all the type classes for interfacing
entailment systems in this sense, including the type class
'Logic.Logic.Logic'.  The entailment relation is given by one or more
theorem provers, rewriters, consistency checkers, model checkers. The
module "Logic.Prover" is for the interface to these.  The data types
'Logic.Prover.Proof_Status' and 'Logic.Prover.Prover' provides the
interface to provers.  In case of a successful proof, also the list of
axioms that have been used in the proof can be returned.

Note that the type class 'Logic.Logic.Logic' contains much more than
just an entailment system. There is infrastructure for parsing,
printing, static analysis (of both basic specifications and symbols
maps) , conversion to ATerms, sublogic recognition etc. You see that
in order to really work with it, one needs much more than just
an entailment system in the mathematical sense.
We will use the term /logic/ synonymously with an extended entailment
system in this sense.

 Module "Logic.Comorphism" provides type classes for the various kinds
of mappings between logics, and module "Logic.Grothendieck"
realizes the Grothendieck logic and also contains a type
'Logic.Grothendieck.LogicGraph'.

/How to add a new logic to Hets/

A good idea is to look at an existing logic, say "Propositional" or
"CASL", and look how it realizes the abstract interface given in
"Logic.Logic" - this is done in "Propositional.Logic_Propositional"
resp. "CASL.Logic_CASL", where the whole of
the "Propositional" resp. "CASL" folder is imported.

You also should have a look at some of the "Common" modules,
providing data structures for identifiers ("Common.Id"),
results ("Common.Result"), and relations
("Common.Lib.Rel"). These are used quite frequently.
-}

module Logic where
