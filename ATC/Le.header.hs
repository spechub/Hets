 
instance ATermConvertible Env where
     toShATerm att0 (Env cm tm as sen env cou) = 
	 let (att1,i1) = toShATerm att0 cm
             (att2,i2) = toShATerm att1 tm
             (att3,i3) = toShATerm att2 as
             (att4,i4) = toShATerm att3 sen 
             (att5,i5) = toShATerm att4 env
             (att6,i6) = toShATerm att5 cou
         in addATerm (ShAAppl "Env" [i1,i2,i3,i4,i5,i6] []) att6
     fromShATerm att = 
         case aterm of
	    (ShAAppl "Env" [i1,i2,i3,i4,i5,i6] _) ->
		let i1'  = fromShATerm (getATermByIndex1 i1 att)
		    i2'  = fromShATerm (getATermByIndex1 i2 att)
                    i3'  = fromShATerm (getATermByIndex1 i3 att)
                    i4' = fromShATerm (getATermByIndex1 i4 att)
                    i5' = fromShATerm (getATermByIndex1 i5 att)
                    i6' = fromShATerm (getATermByIndex1 i6 att)
                in (Env i1' i2' i3' i4' i5' i6')
         where
         aterm = getATerm att
