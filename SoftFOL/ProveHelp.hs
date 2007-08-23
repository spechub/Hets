{- |
Module      :  $Header$
Description :  SPASS help information for the GUI prover.
Copyright   :  (c) Klaus Lüttich, Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@informatik.uni-bremen.de
Stability   :  provisional
Portability :  needs POSIX

Only one String constant carrying the Help information of SPASS.
Maybe it will be replaced by reading an external file.
-}

module SoftFOL.ProveHelp where

spassHelpText :: String
spassHelpText =
  "If you want to add your own options for controlling SPASS make sure you \n"++
  "start with -Auto=0. This switches off the automatic selection of rules\n\n"++
  "The following text is a quotation from: \n"++
  "    \"SPASS Version 2.0\" by Christoph Weidenbach et.al.\n"++
  "   (This document is part of the SPASS-2.1 source distribution)\n\n"++
  "Each reference listed here refers to this document!\n\n"++
  "Literal Quotation (p. 48 and 49):\n\n"++
  "  The options discussed here apply to SPASS Versions 2.0. Options can be \n"++
  "set to integer values. For boolean options 0 means falsity and 1 means \n"++
  "truth. For example, the option -IMPm=1 enables the inference rule merging\n"++
  "paramodulation which can be abbreviated by -IMPm whereas -IMPm=0 disables\n"++
  "the inference rule.\n"++ 
  "\nA.1. Control\n\n"++
  "   Auto        Automatic Mode, after a problem analysis, \n"++
  "               all options are set automatically.\n"++
  "   FullRed     Full Reduction, Section 3. If full reduction is enabled,\n"++
  "               the overall SPASS loop corresponds to the loop presented\n"++
  "               in Table 1, if the option is disabled, it corresponds to\n"++
  "               the lazy reduction loop presented in Table 3.\n"++ 
  "   BoundMode   Bound Mode selects the mode for resource controlled\n"++
  "               generation of the search space, Section 3. \n"++
  "               If set to 1 clauses are weight restricted, if set to \n"++
  "               2 clauses are depth restricted. \n"++
  "   BoundStart  Bound Start determines the start value for resource \n"++
  "               restriction, Section 3.\n"++
  "   BoundLoops  Bound Loops determines the number of resource \n"++
  "               restricted main-loop iterations.\n"++ 
  "\nA.2. Inference Rules\n\n"++ 
  "   ISoR        Sort Constraint Resolution, Definition 4.3.\n"++
  "   IEmS        Empty Sort, Definition 4.4.\n"++ 
  "   IEqR        Equality Resolution, Definition 4.7.\n"++ 
  "   IERR        Reflexivity Resolution, Definition 4.7.\n"++
  "   ISpL        Superposition Left, Definition 4.8.\n"++ 
  "   IOPm        Ordered Paramodulation, Definition 4.8 and Definition 4.9.\n"++
  "   ISPm        (Standard) Paramodulation, Definition 4.8 and Definition 4.9.\n"++
  "   ISpR        Superposition Right, Definition 4.9.\n"++
  "   IOFc        Ordered Factoring, Definition 4.10.\n"++
  "   ISFc        (Standard) Factoring, Definition 4.10.\n"++
  "   IEqF        Equality Factoring, Definition 4.11.\n"++
  "   IMPm        Merging Paramodulation, Definition 4.12.\n"++
  "   IORe        Ordered Resolution, Definition 4.13.\n"++
  "   ISRe        (Standard) Resolution, Definition 4.13.\n"++
  "   IOHy        Ordered Hyper Resolution, Definition 4.14.\n"++
  "   ISHy        (Standard) Hyper Resolution, Definition 4.14.\n"++
  "   Splits      Splitting, Definition 4.25. The option determines the \n"++
  "               number of splitting applications where any negative \n"++
  "               number means that splitting is not restricted.\n"++
  "\nA.3. Reduction Rules\n\n"++
  "   RSSi        Sort Simplification, Definition 4.5.\n"++
  "   RSST        Static Soft Typing, Definition 4.6.\n"++
  "   RObv        Trivial Literal Elimination, Definition 4.15.\n"++
  "   RFSub       Forward Subsumption Deletion, Definition 4.16, Table 5.\n"++
  "   RBSub       Backward Subsumption Deletion, Definition 4.16, Table 6.\n"++
  "   RCon        Condensation, Definition 4.17.\n"++
  "   RTaut       Tautology Deletion, Definition 4.18. If the option is set\n"++
  "               to 1 only syntactic tautologies are eliminated. If it is\n"++
  "               set to 2, semantic tautologies are deleted as well.\n"++
  "   RUnC        Unit Conflict, Definition 4.19.\n"++
  "   RTer        Terminator, Definition 4.19, where the value of the option\n"++
  "               determines the number of non-unit clause occurrences in \n"++
  "               the searched refutation.\n"++
  "   RFMMR       Forward Matching Replacement Resolution, Definition 4.20,\n"++
  "               Table 5.\n"++
  "   RBMMR       Backward Matching Replacement Resolution, Definition 4.20,\n"++
  "               Table 6.\n"++
  "   RFRew       Forward Rewriting, Definition 4.21 and Definition 4.22, Table 5.\n"++
  "   RBRew       Backward Rewriting, Definition 4.21, Table 6.\n"++
  "   RAED        Assignment Equation Deletion, Definition 4.24. If set to 2,\n"++
  "               it is assumed that any model has a non-trivial domain and\n"++
  "               the corresponding eliminations are performed.\n"
