module Common.Precedence where

import Common.Id
import Common.GlobalAnnotations
import Common.AS_Annotation

begPlace, endPlace :: Id -> Bool
begPlace (Id toks _ _) = not (null toks) && isPlace (head toks)
endPlace (Id toks _ _) = not (null toks) && isPlace (last toks)

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg op num = begPlace op && num == 0
isRightArg op num = endPlace op && num + 1 == placeCount op

comparePrecs :: GlobalAnnos -> Bool -> AssocEither -> Id -> Id -> Bool
comparePrecs ga isInfixOp ass arg op = 
    case precRel (prec_annos ga) op arg of
    BothDirections -> False
    rel -> case (begPlace arg, endPlace arg, isInfixOp) of
	   (True, True, True) -> case rel of -- arg and op are infixes
				 Lower -> True
				 NoDirection -> arg == op && 
					  isAssoc ass (assoc_annos ga) op
				 _ -> False
	   (True, True, False) -> False 
            -- infix arg binds weaker than non-infix op
	   (False, True, False) -> ARight == ass
            -- prefix arg binds weaker than postfix op
            -- (not possible on the right side)
	   _ -> True

checkPrecs :: GlobalAnnos -> Id -> Id -> Int -> Bool
checkPrecs ga arg op num =
    if isLeftArg op num 
    then comparePrecs ga (endPlace op) ALeft arg op
    else if isRightArg op num 
    then comparePrecs ga (begPlace op) ARight arg op
    else True 
