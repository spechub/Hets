-- begin header

instance (ATermConvertible a) => ATermConvertible (Annoted a) where
    toShATerm att0 (Annoted aa bb cc dd) =
       case toShATerm att0 aa of { (att1,aa') ->
       case toShATerm att1 bb of { (att2,bb') ->
       case toShATerm att2 cc of { (att3,cc') ->
       case toShATerm att3 dd of { (att4,dd') ->
	 addATerm (ShAAppl "Annoted"  [aa',bb',cc',dd'] []) att4}}}}
    fromShATerm att =
	case aterm of
	    (ShAAppl "Annoted" [ aa, bb, cc, dd ] _) ->
	        case fromShATerm (getATermByIndex1 aa att) of { aa' ->
	        case fromShATerm (getATermByIndex1 bb att) of { bb' ->
	        case fromShATerm (getATermByIndex1 cc att) of { cc' ->
	        case fromShATerm (getATermByIndex1 dd att) of { dd' ->
                   Annoted aa' bb' cc' dd' }}}}
            _ -> fromShATermError "Annoted" aterm
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Annoted\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Annoted\""

-- end header

