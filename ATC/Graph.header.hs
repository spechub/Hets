
-- begin header

instance (ATermConvertible a,
	  ATermConvertible b) => ATermConvertible (Graph a b) where
    toShATerm att0 graph =
       case toShATerm att0 (labNodes graph) of { (att1,aa') ->
       case toShATerm att1 (labEdges graph) of { (att2,bb') ->
	  addATerm (ShAAppl "Graph"  [ aa' , bb' ] []) att2}}
    fromShATerm att =
	case aterm of
	    (ShAAppl "Graph" [ aa , bb ] _) ->
		case fromShATerm (getATermByIndex1 aa att) of { aa' ->
                case fromShATerm (getATermByIndex1 bb att) of { bb' ->
		    mkGraph aa' bb' }}
	    u -> fromShATermError "Graph" u
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Graph\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Graph\""

--end header

