module Comorphisms.HC2I_Utils where

import Common.Id

getNameOfOpId :: Id -> String
getNameOfOpId (Id [] _ _) = error "[Comorphims.HasCASL2IsabelleHOL] Operation without name"
getNameOfOpId (Id (tok:toks) a b) = 
  if (tokStr tok) == "__" then getNameOfOpId (Id toks a b)
    else tokStr tok
