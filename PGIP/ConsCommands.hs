{- |
Module      :$Header$
Description : CMDL interface commands
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

PGIP.ConsCommands contains all commands
related to consistency\/conservativity checks
-}

module PGIP.ConsCommands
       ( cConsChecker
       , cConservCheck
       , cConservCheckAll
       , cConsistCheck
       , cConsistCheckAll
       ) where

import PGIP.DataTypes


cConsChecker:: String -> CMDL_State -> IO CMDL_State
cConsChecker _ state=
	return state

cConservCheck:: String -> CMDL_State -> IO CMDL_State
cConservCheck _ state = 
	return state

cConservCheckAll :: CMDL_State -> IO CMDL_State
cConservCheckAll state =
	return state

cConsistCheck :: String -> CMDL_State -> IO CMDL_State
cConsistCheck _ state = 
	return state

cConsistCheckAll :: CMDL_State -> IO CMDL_State
cConsistCheckAll state =
	return state
