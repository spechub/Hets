
import Haskell.Hatchet.FiniteMaps

{-| Exclude: State |-}
{-| Exclude: Binding |-}
{-| Exclude: VarName |-}
{-| Exclude: KI |-}
{-| Exclude: Qual |-}
{-| Exclude: Assump |-}

instance ShATermConvertible Assump where
    toShATerm att0 (an :>: s) =
       case toShATerm att0 an of { (att1,an') ->
       case toShATerm att1 s  of {  (att2,s') ->
	 addATerm (ShAAppl "Assump_"   [an',s'] []) att2 }}
    fromShATerm att =
	case aterm of
	    (ShAAppl "Assump_" [an',s' ] _) ->
	       case fromShATerm (getATermByIndex1 an' att) of { an ->
	       case fromShATerm (getATermByIndex1 s' att)  of { s  ->
	        (an :>: s) }}
	    u -> fromShATermError "Assump" u
	where
	    aterm = getATerm att

instance (ShATermConvertible a) => ShATermConvertible (Qual a) where
    toShATerm att0 (p :=> t) =
	case toShATerm att0 p of { (att1,p') ->
	case toShATerm att1 t of { (att2,t') ->	 
	 addATerm (ShAAppl "Qual_"   [p',t'] []) att2}}
    fromShATerm att =
	case aterm of
	    (ShAAppl "Qual_" [an',s' ] _) ->
		case fromShATerm (getATermByIndex1 an' att) of { an ->
		case fromShATerm (getATermByIndex1 s' att)  of { s  ->
	         (an :=> s) }}
	    u -> fromShATermError "Qual" u
	where
	    aterm = getATerm att

instance (Ord a, ShATermConvertible a, ShATermConvertible b) => 
    ShATermConvertible (FiniteMap a b) where
    toShATerm att fm = toShATerm att $ toListFM fm 
    fromShATerm att  = listToFM $ fromShATerm att
