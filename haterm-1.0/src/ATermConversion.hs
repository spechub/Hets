module ATermConversion where

import ATermAbstractSyntax
import ATermReadWrite

class ATermConvertible t where
  toATerm   :: t -> ATerm
  fromATerm :: ATerm -> t

toATermString t		= writeATerm (toATerm t)
toSharedATermString t	= writeSharedATerm (toATerm t)
fromATermString s 	= fromATerm (readATerm s)

fromATermError t u = error ("Cannot convert ATerm to "++t++": "++(show u))
