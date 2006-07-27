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

commands::[ ([String], CommandFunctionsAndParameters)]
commands =     [(["use","PATH"],                                       (CommandParam commandUse [])), -- Static.AnalysisLibrary, Driver.ReadFn
                (["dg","auto","GOALS"],                                (CommandParamStatus commandDgAuto        [] )), -- Proofs.Auto
                (["dg","glob-subsume","GOALS"],                        (CommandParamStatus commandDgGlobSubsume [] )), -- Proofs.Global
                (["dg","glob-decomp","GOALS"],                         (CommandParamStatus commandDgGlobDecomp  [] )), -- Proofs.Global
                (["dg","loc-infer","GOALS"],                           (CommandParamStatus commandDgLocInfer    [] )), -- Proofs.Local
                (["dg","loc-decomp","GOALS"],                          (CommandParamStatus commandDgLocDecomp   [] )), -- Proofs.Local
                (["dg","comp","GOALS"],                                (CommandParamStatus commandDgComp        [] )), -- Proofs.Comp
                (["dg","comp-new","GOALS"],                            (CommandParamStatus commandDgCompNew     [] )), -- Proofs.Comp
                (["dg","hide-thm","GOALS"],                            (CommandParamStatus commandDgHideThm     [] )), -- Proofs.HideThmShift
                (["dg","thm-hide","GOALS"],                            (CommandTest test [])), -- Proofs.ThmHideShift
                (["dg","basic","GOALS"],                               (CommandParamStatus commandDgInferBasic  [] )), -- Proofs.InferBasic
                (["dg-all","auto"],                                    (CommandStatus commandDgAllAuto             )), -- dto.
                (["dg-all","glob-subsume"],                            (CommandStatus commandDgAllGlobSubsume      )),
                (["dg-all","glob-decomp"],                             (CommandStatus commandDgAllGlobDecomp       )),
                (["dg-all","loc-infer"],                               (CommandStatus commandDgAllLocInfer         )),
                (["dg-all","loc-decomp"],                              (CommandStatus commandDgAllLocDecomp        )),
                (["dg-all","comp"],                                    (CommandStatus commandDgAllComp             )),
                (["dg-all","comp-new"],                                (CommandStatus commandDgAllCompNew          )),
                (["dg-all","hide-thm"],                                (CommandStatus commandDgAllHideThm          )),
                (["dg-all","thm-hide"],                                (CommandStatus commandDgAllThmHide          )),
                (["dg-all","basic"],                                   (CommandStatus commandDgAllInferBasic       )),
                (["show-dg-goals"],                                    (CommandShowStatus commandShowDgGoals       )), -- new function
--                (["show-dg-goals"],                                    (CommandTest test [])),
                (["show-theory-goals"],                                (CommandShowStatus commandShowTheory        )),
                (["show-theory"],                                      (CommandShowStatus commandShowNodeTheory    )), -- dto.
                (["node-info"],                                        (CommandShowStatus commandShowNodeInfo      )), -- GUI.ConvertAbstractToDevGraph
                (["show-taxonomy"],                                    (CommandTest test [])), --  GUI.ConvertAbstractToDevGraph
                (["show-concepts"],                                    (CommandTest test [])), --  GUI.ConvertAbstractToDevGraph
                (["translate","COMORPHISM"],                           (CommandTest test [])), -- Proofs.InferBasic
                (["prover","PROVER"],                                  (CommandTest test [])), -- Proofs.InferBasic
                (["proof-script","FORMULA","PROOF-SCRIPT"],            (CommandTest test [])), -- Isabelle.IsaProve.hs (for Isabelle)
                (["cons-check", "PROVER"],                             (CommandTest test [])), -- ISabelle.IsaProve.hs (for ISabelle)
                (["prove", "FORMULA-STAR","using","FORMULA-PLUS"],     (CommandTest test [])), -- Proofs.InferBasic
                (["prove", "FORMULA-STAR","excluding","FORMULA-PLUS"], (CommandTest test [])), -- Proofs.InferBasic
                (["prove", "FORMULA-STAR"],                            (CommandTest test [])), -- Proofs.InferBasic
                (["prove-all","using","FORMULA-PLUS"],                 (CommandTest test [])), -- dto.
                (["prove-all","excluding","FORMULA-PLUS"],             (CommandTest test [])),
                (["prove-all"],                                        (CommandTest test []))]


