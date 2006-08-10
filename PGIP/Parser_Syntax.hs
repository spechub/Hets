{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Definition of the command line script syntax. Any command from the script is defined by a list of strings and keywords (PATH, GOALS, COMORPHISM,PROVER,
FORMULA, PROOF-SCRIPT, FORMULA-STAR, FORMULA-PLUS) and a function toghether with a list of parameters. If the parser manages to parse in the given 
order all the indicatad words it will execute the corresponding function passing as argument a list of parameters. The parameters are determined
by the keywords enumarated above. The meaning of each is
PATH - the parser expects to read a path
GOALS - the parser expects to read none or more goals
COMORPHISM - the parser expects to read one or more ID separated by semicolon
PROVER - the parser expects to read a prover ID
FORMULA - the parser expects to read a formula ID
PROOF-SCRIPT - the parser expects to read some strings ended with the keyword end-script 
FORMULA-STAR - the parser expects to read none or more formulaes separated by blanks
FURMULA-PLUS - the parser expects to read one or more formulaes separated by blanks
If the parser meaneage to parse in the given order all the indicated words

-} 



module PGIP.Parser_Syntax where

import PGIP.Commands
import PGIP.Common
   
        -- basic datastructures: see Static.DevGraph, Logic.Prover 

commands::[ ([String],InterpreterCmd )]
commands 
 =[(["use","PATH"],
                                                 (CmdP   cUse           [])),
   (["dg","auto","GOALS"],
                                                 (CmdPS  cDgAuto        [])), 
   (["dg","glob-subsume","GOALS"],
                                                 (CmdPS  cDgGlobSubsume [])), 
   (["dg","glob-decomp","GOALS"],
                                                 (CmdPS  cDgGlobDecomp  [])), 
   (["dg","loc-infer","GOALS"],
                                                 (CmdPS  cDgLocInfer    [])), 
   (["dg","loc-decomp","GOALS"],
                                                 (CmdPS  cDgLocDecomp   [])), 
   (["dg","comp","GOALS"],
                                                 (CmdPS  cDgComp        [])), 
   (["dg","comp-new","GOALS"],
                                                 (CmdPS  cDgCompNew     [])), 
   (["dg","hide-thm","GOALS"],
                                                 (CmdPS  cDgHideThm     [])), 
   (["dg","thm-hide","GOALS"],
                                                 (CmdT   test           [])), 
   (["dg","basic","GOALS"],
                                                 (CmdPS  cDgInferBasic  [])), 
   (["dg-all","auto"],
                                                 (CmdS   cDgAllAuto       )), 
   (["dg-all","glob-subsume"],
                                                 (CmdS   cDgAllGlobSubsume)),
   (["dg-all","glob-decomp"],
                                                 (CmdS   cDgAllGlobDecomp )),
   (["dg-all","loc-infer"],
                                                 (CmdS   cDgAllLocInfer   )),
   (["dg-all","loc-decomp"],
                                                 (CmdS   cDgAllLocDecomp  )),
   (["dg-all","comp"],
                                                 (CmdS   cDgAllComp       )),
   (["dg-all","comp-new"],
                                                 (CmdS   cDgAllCompNew    )),
   (["dg-all","hide-thm"],
                                                 (CmdS   cDgAllHideThm    )),
   (["dg-all","thm-hide"],
                                                 (CmdS   cDgAllThmHide    )),
   (["dg-all","basic"],
                                                 (CmdS   cDgAllInferBasic )),
   (["show-dg-goals"],
                                                 (CmdSS  cShowDgGoals     )), 
   (["show-theory-goals"],
                                                 (CmdSS  cShowTheory      )),
   (["show-theory"],
                                                 (CmdSS  cShowNodeTheory  )), 
   (["node-info"],
                                                 (CmdSS  cShowNodeInfo    )), 
   (["show-taxonomy"],
                                                 (CmdSS  cShowNodeTaxonomy)), 
   (["show-concepts"],
                                                 (CmdSS  cShowNodeConcept )), 
   (["translate","COMORPHISM"],
                                                 (CmdPS  cTranslate     [])), 
   (["prover","PROVER"],
                                                 (CmdPS  cProver        [])), 
   (["proof-script","FORMULA","PROOF-SCRIPT"],
                                                 (CmdT   test           [])), 
   (["cons-check", "PROVER"],
                                                 (CmdT   test           [])), 
   (["prove-all","using","FORMULA-PLUS"],
                                                 (CmdT   test           [])), 
   (["prove-all","excluding","FORMULA-PLUS"],
                                                 (CmdT   test           [])),
   (["prove-all"],
                                                 (CmdT test             [])),
   (["prove", "FORMULA-STAR","using","FORMULA-PLUS"],
                                                 (CmdT   test           [])), 
   (["prove", "FORMULA-STAR","excluding","FORMULA-PLUS"],
                                                 (CmdT   test           [])), 
   (["prove", "FORMULA-STAR"],
                                                 (CmdT   test           []))]
 

