-- begin header

import CASL.Sublogic

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

instance ATermConvertible CASL_Sublogics where
    toShATerm att (CASL_SL b1 b2 b3 b4 b5 for) =
       let (att1,i1) = toShATerm att b1
           (att2,i2) = toShATerm att1 b2
           (att3,i3) = toShATerm att2 b3
           (att4,i4) = toShATerm att3 b4
           (att5,i5) = toShATerm att4 b5
           (att6,i6) = toShATerm att5 for
       in addATerm (ShAAppl "CASL_Sublogics" [i1,i2,i3,i4,i5,i6] []) att6 
    fromShATerm att = case aterm of
                       (ShAAppl "CASL_Sublogics" [i1,i2,i3,i4,i5,i6] []) ->
                         let i1' = fromShATerm (getATermByIndex1 i1 att)
                             i2' = fromShATerm (getATermByIndex1 i2 att)
                             i3' = fromShATerm (getATermByIndex1 i3 att)
                             i4' = fromShATerm (getATermByIndex1 i4 att)
                             i5' = fromShATerm (getATermByIndex1 i5 att)
                             i6' = fromShATerm (getATermByIndex1 i6 att)
                         in (CASL_SL i1' i2' i3' i4' i5' i6')
                      where aterm = getATerm att



instance ATermConvertible CASL_Formulas where
    toShATerm att Atomic = addATerm (ShAAppl "Atomic" [] []) att
    toShATerm att Horn = addATerm (ShAAppl "Horn" [] []) att
    toShATerm att GHorn = addATerm (ShAAppl "GHorn" [] []) att
    toShATerm att FOL = addATerm (ShAAppl "FOL" [] []) att   
    fromShATerm att = case aterm of
                       (ShAAppl "Atomic" [] []) -> Atomic
		       (ShAAppl "Horn" [] []) -> Horn
		       (ShAAppl "GHorn" [] []) -> GHorn
		       (ShAAppl "FOL" [] []) -> FOL
                      where aterm = getATerm att
-- end header




