
import Haskell.Hatchet.FiniteMaps

{-| Exclude: State |-}
{-| Exclude: Binding |-}
{-| Exclude: VarName |-}
{-| Exclude: KI |-}
{-| Exclude: Qual |-}
{-| Exclude: Assump |-}

instance ATermConvertible Assump where
    toShATerm att0 (an :>: s) =
	let (att1,an') = toShATerm att0 an
	    (att2,s') = toShATerm att1 s 
	    lat = [an',s']
	in addATerm (ShAAppl "Assump_"  lat []) att2
    fromShATerm att =
	case aterm of
	    (ShAAppl "Assump_" [an',s' ] _) ->
		let an = fromShATerm (getATermByIndex1 an' att)
		    s  = fromShATerm (getATermByIndex1 s' att)
	        in (an :>: s)
	    u -> fromShATermError "Assump" u
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Assump\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Assump\""

instance (ATermConvertible a) => ATermConvertible (Qual a) where
    toShATerm att0 (p :=> t) =
	let (att1,p') = toShATerm att0 p
	    (att2,t') = toShATerm att1 t 
	    lat = [p',t']
	in addATerm (ShAAppl "Qual_"  lat []) att2
    fromShATerm att =
	case aterm of
	    (ShAAppl "Qual_" [an',s' ] _) ->
		let an = fromShATerm (getATermByIndex1 an' att)
		    s  = fromShATerm (getATermByIndex1 s' att)
	        in (an :=> s)
	    u -> fromShATermError "Qual" u
	where
	    aterm = getATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"Qual\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"Qual\""


instance (Ord a, ATermConvertible a, ATermConvertible b) => 
    ATermConvertible (FiniteMap a b) where
    toShATerm att fm = toShATerm att $ toListFM fm 
    fromShATerm att  = listToFM $ fromShATerm att
    fromATerm _ = error "function \"fromATerm\" not derived (implemented) for data type \"FiniteMap\""
    toATerm _ = error "function \"toATerm\" not derived (implemented) for data type \"FiniteMap\""
