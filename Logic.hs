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

The type class 'Logic.Logic.LogicalFramework' is an interface for the
logics which can be used as logical frameworks, in which object
logics can be specified by the user. Its methods are used in the
analysis of newlogic definitions, in "Framework.Analysis".

The method 'Logic.Logic.LogicalFramework.base_sig'
returns the base signature of the framework
The method 'Logic.Logic.LogicalFramework.write_logic'
constructs the contents of the Logic_L
file, where L is the name of the object logic passed as an argument.
Typically, this file will declare the lid of the object logic L and
instances of the classes Language, Syntax, Sentences, Logic, and
StaticAnalysis. The instance of Category is usually inherited from
the framework itself as the object logic reuses the signatures and
morphisms of the framework. The function
'Logic.Logic.LogicalFramework.write_syntax' constructs
the contents of the file declaring the Ltruth morphism.
Currently we simply store the morphism using its representation as
a Haskell datatype value.

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
