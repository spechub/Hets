-- begin header



instance ATermConvertible Morphism where
    toShATerm att0 (Morphism ms mt)=
	let (att1,i1) = toShATerm att0 ms
            (att2,i2) = toShATerm att1 mt           
            lat = [i1,i2]
	in addATerm (ShAAppl "Morphism"  lat []) att2
    fromShATerm att =
	case aterm of
	    (ShAAppl "Morphism" [i1,i2 ] _) ->
		let ms = fromShATerm $ getATermByIndex1 i1 att 
		    mt = fromShATerm $ getATermByIndex1 i2 att 
                in (Morphism ms mt)
	    u -> fromShATermError "Morphism" u
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Morphism\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Morphism\""

instance (ATermConvertible t) => ATermConvertible (Qual t)where
   toShATerm att0 (predlist :=> t) = 
       let (att1,i1) = toShATerm att0 predlist
           (att2,i2) = toShATerm att1 t
       in addATerm (ShAAppl "Qual" [i1,i2] []) att2
   fromShATerm att = 
       case aterm of
           (ShAAppl "Qual" [i1,i2] _) -> 
	       let predlist = fromShATerm $ getATermByIndex1 i1 att
                   t = fromShATerm $ getATermByIndex1 i2 att
               in (predlist :=> t)
	   u -> fromShATermError "Qual" u
       where aterm = getATerm att
   fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Qual\""
   toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Qual\""

 
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
	    u -> fromShATermError "Env" u
         where
         aterm = getATerm att
     fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Env\""
     toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Env\""


instance ATermConvertible OpInfos where
   toShATerm att0 (OpInfos lop) = 
                     let (att1,i1) = toShATerm att0 lop
                     in addATerm (ShAAppl "OpInfos" [i1] []) att1
   fromShATerm att = 
       case aterm of
           (ShAAppl "OpInfos" [i1] []) -> 
	       let lop = fromShATerm $ getATermByIndex1 i1 att
               in (OpInfos lop)
	   u -> fromShATermError "OpInfos" u
       where aterm = getATerm att
   fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"OpInfos\""
   toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"OpInfos\""

-- end header