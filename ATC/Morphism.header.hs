
instance ATermConvertible Morphism where
    toShATerm att0 (Morphism msource mtarget)=
	let (att1,i1) = toShATerm att0 msource
            (att2,i2) = toShATerm att1 mtarget           
            lat = [i1,i2]
	in addATerm (ShAAppl "Morphism"  lat []) att2
    fromShATerm att =
	case aterm of
	    (ShAAppl "Morphism" [i1,i2 ] _) ->
		let msource = fromShATerm $ getATermByIndex1 i1 att 
		    mtarget = fromShATerm $ getATermByIndex1 i2 att 
                in (Morphism msource mtarget)
	where
	    aterm = getATerm att
