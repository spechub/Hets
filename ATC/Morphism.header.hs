
instance ATermConvertible Morphism where
    toShATerm att0 (Morphism msource mtarget)=
       case toShATerm att0 msource of { (att1,i1) ->
       case toShATerm att1 msource of { (att2,i2) ->            
	 addATerm (ShAAppl "Morphism"   [i1,i2] []) att2}}
    fromShATerm att =
	case aterm of
	    (ShAAppl "Morphism" [i1,i2 ] _) ->
		case fromShATerm $ getATermByIndex1 i1 att of { msource ->
		case fromShATerm $ getATermByIndex1 i2 att of { mtarget ->
                 (Morphism msource mtarget)}}
	    u -> fromShATermError "Morphism" u
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Morphism\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Morphism\""
