-- begin header


instance (ATermConvertible t) => ATermConvertible (Qual t)where
   toShATerm att0 (predlist :=> t) = 
      case toShATerm att0 predlist of {  (att1,i1) ->
      case toShATerm att1 t of {  (att2,i2) ->
         addATerm (ShAAppl "Qual" [i1,i2] []) att2}}
   fromShATerm att = 
       case aterm of
           (ShAAppl "Qual" [i1,i2] _) -> 
	       case fromShATerm $ getATermByIndex1 i1 att of { predlist ->
               case fromShATerm $ getATermByIndex1 i2 att of { t ->
                  predlist :=> t }}
	   u -> fromShATermError "Qual" u
       where aterm = getATerm att
   fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Qual\""
   toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Qual\""

 
-- end header
