
{- HetCATS/P_user_state.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002
   
   This are the data structures needed to initialize and manipulate the 
   user state for the Parsec parsers. Usually it is initialized at the 
   beginning of parse and updated every time an %logic, %hide or %with
   occurs. So it is needed by HetCATS/Anno_Parser.hs

-}

module P_user_state (init_user_state,update_logic,
		     update_sublogic,cur_logic,
		     initial_state) 
where

import Parsec
-- import LogicGraph

data UserState = UserState { cur_logic :: String
			   } deriving (Show,Eq)

initial_state = UserState {cur_logic = "CASL"}

init_user_state id = (setState (UserState { cur_logic = id }))

update_logic ln = updateState (\st -> st { cur_logic = (conv_logic ln) })
    where conv_logic ln = ln
--	  conv_logic ln = lookup_logic ln the_logic_list

update_sublogic (ln,sln) = 
    updateState (\st ->st {cur_logic = (conv_logic ln) })
	where conv_logic ln = ln
--	      conv_logic ln = 
--	          lookup_logic sln 
--			      (all_logics (lookup_logic ln the_logic_list))

{-
lookup_logic s ls = s
lookup_logic s ls = case (lookup_logic' s ls) of 
		    Just l  -> l
		    Nothing -> error ("*** Unknown logic: " ++ s)
    where lookup_logic' ln [] = Nothing
	  lookup_logic' ln l:ls = if (logic_name l) == ln then
				  l
				  else
				  (case (lookup_logic' ln (all_sublogics l)) of
				   Just sl -> sl
				   Nothing -> lookup_logic s ls)
-}