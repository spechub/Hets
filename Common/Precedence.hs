
{- |
Module      :  $Header$
Copyright   :  Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable
    
   precedence check for the mixfix analysis

-}

module Common.Precedence where

import Common.Id
import Common.GlobalAnnotations
import Common.AS_Annotation

-- | 'Id' starts with a 'Place'
begPlace :: Id -> Bool
begPlace (Id toks _ _) = not (null toks) && isPlace (head toks)
-- | 'Id' ends with a 'Place'
endPlace :: Id -> Bool
endPlace (Id toks _ _) = not (null toks) && isPlace (last toks)

-- | check if a left argument will be added.
-- (The 'Int' is the number of current arguments.)
isLeftArg :: Id -> Int -> Bool
isLeftArg op num = begPlace op && num == 0
-- | check if a right argument will be added.
isRightArg :: Id -> Int -> Bool
isRightArg op num = endPlace op && num + 1 == placeCount op

-- | compare precedences of a left or right argument and a top-level operator.
-- (The 'Bool' indicates if the operator is any infix .)
comparePrecs :: GlobalAnnos -> Bool -> AssocEither -> Id -> Id -> Bool
comparePrecs ga isInfixOp ass arg op = 
    case precRel (prec_annos ga) op arg of
    BothDirections -> False
    rel -> case (begPlace arg, endPlace arg, isInfixOp) of
	   (True, True, True) -> case rel of -- arg and op are infixes
				 Lower -> True
				 NoDirection -> if arg == op then 
					  isAssoc ass (assoc_annos ga) op
						  else True
				 _ -> False 
	   (True, True, False) -> False 
            -- infix arg binds weaker than non-infix op
	   (False, True, False) -> ARight == ass
            -- prefix arg binds weaker than postfix op
            -- (not possible on the right side)
	   _ -> True

-- | check precedences of an argument and a top-level operator.
-- (The 'Int' is the number of current arguments of the operator.)
checkPrecs :: GlobalAnnos -> Id -> Id -> Int -> Bool
checkPrecs ga arg op num =
    if isLeftArg op num 
    then comparePrecs ga (endPlace op) ALeft arg op
    else if isRightArg op num 
    then comparePrecs ga (begPlace op) ARight arg op
    else True 
