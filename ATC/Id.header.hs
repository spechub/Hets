-- <header>
import Common.Lib.Parsec.Pos

instance ATermConvertible SourcePos where
    toShATerm att0 sourcepos =            --(SourcePos aa bb cc) =
	let (att1,aa') = toShATerm att0 $ sourceName sourcepos
            (att2,bb') = toShATerm att1 $ sourceLine sourcepos
            (att3,cc') = toShATerm att2 $ sourceColumn sourcepos
	    lat = [ aa' , bb' , cc' ]
	in addATerm (ShAAppl "SourcePos"  lat []) att3
    fromShATerm att =
	case aterm of
	    (ShAAppl "SourcePos" [ aa , bb , cc] _) ->
		let aa' = fromShATerm (getATermByIndex1 aa att)
                    bb' = fromShATerm (getATermByIndex1 bb att)
                    cc' = fromShATerm (getATermByIndex1 cc att)
		    in (newPos aa' bb' cc')
	where
	    aterm = getATerm att
-- </header>
