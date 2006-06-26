{- |
Module      :$Header$
Copyright   : uni-bremen and Razvan Pascanu
Licence     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@iu-bremen.de
Stability   : provisional
Portability : portable

Definition of the command line script syntax

   TODO
        - add comments
        
-} 



module PGIP.Parser_Syntax where

import PGIP.Commands
   
        -- basic datastructures: see Static.DevGraph, Logic.Prover 

commands::[ ([String], CommandFunctionsAndParameters)]
commands =     [(["use","PATH"],                                       (CommandIO commandUse [])), -- Static.AnalysisLibrary, Driver.ReadFn
                (["dg","auto","GOALS"],                                (CommandTest test [])), -- Proofs.Auto
                (["dg","glob-subsume","GOALS"],                        (CommandTest test [])), -- Proofs.Global
                (["dg","glob-decomp","GOALS"],                         (CommandTest test [])), -- Proofs.Global
                (["dg","loc-infer","GOALS"],                           (CommandTest test [])), -- Proofs.Local
                (["dg","loc-decomp","GOALS"],                          (CommandTest test [])), -- Proofs.Local
                (["dg","comp","GOALS"],                                (CommandTest test [])), -- Proofs.Comp
                (["dg","comp-new","GOALS"],                            (CommandTest test [])), -- Proofs.Comp
                (["dg","hide-thm","GOALS"],                            (CommandTest test [])), -- Proofs.HideThmShift
                (["dg","thm-hide","GOALS"],                            (CommandTest test [])), -- Proofs.ThmHideShift
                (["dg","basic","GOALS"],                               (CommandTest test [])), -- Proofs.InferBasic
                (["dg-all","auto"],                                    (CommandTest test [])), -- dto.
                (["dg-all","glob-subsume"],                            (CommandTest test [])),
                (["dg-all","glob-decomp"],                             (CommandTest test [])),
                (["dg-all","loc-infer"],                               (CommandTest test [])),
                (["dg-all","loc-decomp"],                              (CommandTest test [])),
                (["dg-all","comp"],                                    (CommandTest test [])),
                (["dg-all","comp-new"],                                (CommandTest test [])),
                (["dg-all","hide-thm"],                                (CommandTest test [])),
                (["dg-all","thm-hide"],                                (CommandTest test [])),
                (["dg-all","basic"],                                   (CommandTest test [])),
                (["show-dg-goals"],                                    (CommandTest test [])), -- new function
                (["show-theory-goals"],                                (CommandTest test [])), -- showTheory in GUI.ConvertAbstractToDevGraph
                (["show-theory"],                                      (CommandTest test [])), -- dto.
                (["node-info"],                                        (CommandTest test [])), -- GUI.ConvertAbstractToDevGraph
                (["show-taxonomy"],                                    (CommandTest test [])), --  GUI.ConvertAbstractToDevGraph
                (["show-concepts"],                                    (CommandTest test [])), --  GUI.ConvertAbstractToDevGraph
                (["translate","COMORPHISM"],                           (CommandTest test [])), -- Proofs.InferBasic
                (["prover","PROVER"],                                  (CommandTest test [])), -- Proofs.InferBasic
                (["proof-script","FORMULA","PROOF-SCRIPT"],            (CommandTest test [])), -- Isabelle.IsaProve.hs (for Isabelle)
                (["cons-check", "PROVER"],                             (CommandTest test [])), -- ISabelle.IsaProve.hs (for ISabelle)
                (["prove", "FORMULA-STAR","with","FORMULA-PLUS"],      (CommandTest test [])), -- Proofs.InferBasic
                (["prove", "FORMULA-STAR","excluding","FORMULA-PLUS"], (CommandTest test [])), -- Proofs.InferBasic
                (["prove", "FORMULA-STAR"],                            (CommandTest test [])), -- Proofs.InferBasic
                (["prove-all","with","FORMULA-PLUS"],                  (CommandTest test [])), -- dto.
                (["prove-all","excluding","FORMULA-PLUS"],             (CommandTest test [])),
                (["prove-all"],                                        (CommandTest test []))]


