{- |
The folder "Logic" contains the infrastructure needed for
presenting a logic to Hets.
The module "Logic.Logic" contains all
the type classes for interfacing institutions mentioned above,
including the type class 'Logic.Logic.Logic'.  The module
"Logic.Prover" is for the interface to theorem provers,
rewriters, consistency checkers, model checkers.  The data types
'Logic.Prover.Proof_Status' and 'Logic.Prover.Prover' provides the interface to
provers.  In case of a successful proof, also the list of axioms that
have been used in the proof can be returned. 

 Module "Logic.Comorphism" provides type classes for the various kinds
of mappings between institutions, and module "Logic.Grothendieck"
realizes the Grothendieck institution and also contains a type
'Logic.Grothendieck.LogicGraph'. 

/How to add a new logic to Hets/

A good idea is to look at an existing logic, say "CASL", and look
how it realizes the abstract interface given in "Logic.Logic" -
this is done in "CASL.Logic_CASL", where the latter module imports
the whole of the "CASL" folder.

You also should have a look at some of the "Common" modules, 
providing data structures for identifiers ("Common.Id"),
sets ("Common.Lib.Set"), maps ("Common.Lib.Map") and relations ("Common.Lib.Rel").
These are used quite frequently.

-}

module Logic where
