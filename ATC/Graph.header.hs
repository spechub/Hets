
-- begin header

instance (ATermConvertible a,
	  ATermConvertible b) => ATermConvertible (Graph a b) where
    toShATerm att0 graph =
	let (att1,aa') = toShATerm att0 $ labNodes graph
            (att2,bb') = toShATerm att1 $ labEdges graph
	    lat = [ aa' , bb' ]
	in addATerm (ShAAppl "Graph" lat []) att1
    fromShATerm att =
	case aterm of
	    (ShAAppl "Graph" [ aa , bb ] _) ->
		let aa' = fromShATerm (getATermByIndex1 aa att)
                    bb' = fromShATerm (getATermByIndex1 bb att)
		    in (mkGraph aa' bb')
	where
	    aterm = getATerm att

--end header

