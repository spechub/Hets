-- begin header


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

 
-- end header
