
-- begin header

instance (ATermConvertible a) => ATermConvertible (Annoted a) where
    toShATerm att0 (Annoted aa bb cc dd) =
	let (att1,aa') = toShATerm att0 aa
            (att2,bb') = toShATerm att1 bb
            (att3,cc') = toShATerm att2 cc
            (att4,dd') = toShATerm att3 dd
            lat = [aa',bb',cc',dd']
	in addATerm (ShAAppl "Annoted"  lat []) att4
    fromShATerm att =
	case aterm of
	    (ShAAppl "Annoted" [ aa, bb, cc, dd ] _) ->
		let aa' = fromShATerm (getATermByIndex1 aa att)
		    bb' = fromShATerm (getATermByIndex1 bb att)
		    cc' = fromShATerm (getATermByIndex1 cc att)
		    dd' = fromShATerm (getATermByIndex1 dd att)
                in (Annoted aa' bb' cc' dd')
            _ -> fromShATermError "Annoted" aterm
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Annoted\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Annoted\""

-- end header

