{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Proof where

import Structured
import Parser
import StaticAnalysis

prove :: LogicGraph -> Bool -> String -> [String] -> IO()
prove logicGraph flat spec raw_goals = do
   if flat then proveFlat th (getGoals th)
           else proveStruct th env (getGoals th)
   where
   as = hetParse logicGraph spec
   Just (env,th) = staticAnalysis as
   getGoals (G_theory id (sig,ax)) =
     map (G_sentence id . parse_sentence id sig) raw_goals

   proveFlat th goals = do
     res <- sequence (map (proveFlat1 th) goals)
     putStrLn (show res)

   proveFlat1 (G_theory id (sig,ax)) (G_sentence _ goal) =
     prover id (sig,ax) (coerce1 goal)

   proveStruct (G_theory id (sig,ax)) env goals = do
     res <- sequence (map (prove1 env) goals)
     putStrLn (show res)
     where
     prove1 :: Env -> G_sentence -> IO Proof_status
     prove1 env g@(G_sentence id goal) = case env of
       Basic_env (G_theory id' (sig,ax)) ->
         prover id' (sig,ax) (coerce1 goal)
       Intra_Translation_env th env' (G_morphism id' mor) ->
         let goal' = coerce1 goal in
         case inv_map_sentence id' mor goal' of
           Just goal'' -> prove1 env' (G_sentence id' goal'')
           Nothing -> proveFlat1 th g
       Inter_Translation_env th env' (G_LTR tr) ->
         prove_aux th
         where
         prove_aux (G_theory _ (sig,_)) =
          case inv_tr_sen tr (coerce1 sig) (coerce1 goal) of
           Just goal'' -> prove1 env' (G_sentence (source tr) goal'')
           Nothing -> proveFlat1 th g
       Extension_env _ env1 env2 -> do
         res <- prove1 env1 g
         case res of
           Proved -> return Proved
           _ -> prove1 env2 g
