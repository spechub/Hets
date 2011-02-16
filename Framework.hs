{-
Description : syntax and analysis for adding object logics to Hets
from their specification in a logical framework

The folder "Framework" contains the infrastructure needed for 
extending Hets with new logics which are specified in 
some logical framework. Currently, this only works for LF, but
reading Isabelle and Maude definitions of logics is also 
possible.

The module "Framework.AS" gives the abstract syntax, while the
static analysis of the newly defined logics is implemented in
the module "Framework.Analysis" and it relies on the methods
provided by the instances of the class 'Logic.Logic.LogicalFramework'.

-}
