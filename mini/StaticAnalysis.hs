module StaticAnalysis where

import Structured

staticAnalysis :: SPEC -> Maybe (Env, G_theory)
staticAnalysis sp = staticAna1 initial_theory sp
  where
  initial_theory = get_initial sp
  get_initial sp = case sp of
    Basic_spec (G_basic_spec logic _) ->
      G_theory logic (empty_theory logic)
    Intra_Translation sp _ -> get_initial sp
    Inter_Translation sp _ -> get_initial sp
    Extension sp _ -> get_initial sp
  staticAna1 :: G_theory -> SPEC -> Maybe (Env, G_theory)
  staticAna1 th@(G_theory id (sig,ax)) sp =
    case sp of
      Basic_spec (G_basic_spec _ b) ->
        do b' <- coerce b
           (sig1,ax1) <- basic_analysis id sig b'
           let th' = G_theory id (sig1,ax1++ax)
           return (Basic_env th',th')
      Intra_Translation sp (G_symbol_mapping_list  _ symap) ->
        do (env,G_theory id1 (sig1,ax1)) <- staticAna1 th sp
           symap' <- coerce symap
           mor <-  stat_symbol_mapping id1 symap' sig1
           tr_ax <- sequence (map (map_sentence id1 mor) ax1)
           let th' = G_theory id1 (cod id1 mor,tr_ax)
           let env' = Intra_Translation_env th' env (G_morphism id1 mor)
           return (env',th')
      Inter_Translation sp (G_LTR tr) ->
        do (env,G_theory id1 (sig1,ax1)) <- staticAna1 th sp
           let id_tar = target tr
           sig2 <- coerce sig1
           ax2 <- coerce ax1
           let tr_sig = tr_sign tr sig2
           tr_ax <- sequence (map (tr_sen tr sig2) ax2)
           let th' = G_theory id_tar (tr_sig,tr_ax)
           let env' = Inter_Translation_env th' env (G_LTR tr)
           return (env',th')
      Extension sp1 sp2 ->
        do (env1,th1) <- staticAna1 th sp1
           (env2,th2) <- staticAna1 th1 sp2
           return (Extension_env th2 env1 env2,th2)
