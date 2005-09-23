-- | Just a trivial extension to Text.XML.HaXml.OneOfN.
--   Needed for Omdoc-Module - not needed by Dtd2Haskell.

module MoreOfN where

import Text.XML.HaXml.Xml2Haskell

data OneOf21 a b c d e f g h i j k l m n o p q r s t u
    = OneOf21 a | TwoOf21 b | ThreeOf21 c | FourOf21 d | FiveOf21 e
    | SixOf21 f | SevenOf21 g | EightOf21 h | NineOf21 i | TenOf21 j
    | ElevenOf21 k | TwelveOf21 l | ThirteenOf21 m | FourteenOf21 n
    | FifteenOf21 o | SixteenOf21 p | SeventeenOf21 q | EighteenOf21 r
    | NineteenOf21 s | TwentyOf21 t | TwentyOneOf21 u
    deriving (Eq,Show)

instance (XmlContent a,XmlContent b,XmlContent c,XmlContent d,XmlContent e
          ,XmlContent f,XmlContent g,XmlContent h,XmlContent i,XmlContent j
          ,XmlContent k,XmlContent l,XmlContent m,XmlContent n,XmlContent o
          ,XmlContent p,XmlContent q,XmlContent r,XmlContent s,XmlContent t
	  ,XmlContent u)
    => XmlContent (OneOf21 a b c d e f g h i j k l m n o p q r s t u)
  where
    fromElem cs =
        (choice OneOf21 $ choice TwoOf21 $ choice ThreeOf21 $ choice FourOf21
        $ choice FiveOf21 $ choice SixOf21 $ choice SevenOf21
        $ choice EightOf21 $ choice NineOf21 $ choice TenOf21
        $ choice ElevenOf21 $ choice TwelveOf21 $ choice ThirteenOf21
        $ choice FourteenOf21 $ choice FifteenOf21 $ choice SixteenOf21
        $ choice SeventeenOf21 $ choice EighteenOf21 $ choice NineteenOf21
        $ choice TwentyOf21 $ choice TwentyOneOf21
        $ (\c->(Nothing,c))) cs
    toElem (OneOf21 x) = toElem x
    toElem (TwoOf21 x) = toElem x
    toElem (ThreeOf21 x) = toElem x
    toElem (FourOf21 x) = toElem x
    toElem (FiveOf21 x) = toElem x
    toElem (SixOf21 x) = toElem x
    toElem (SevenOf21 x) = toElem x
    toElem (EightOf21 x) = toElem x
    toElem (NineOf21 x) = toElem x
    toElem (TenOf21 x) = toElem x
    toElem (ElevenOf21 x) = toElem x
    toElem (TwelveOf21 x) = toElem x
    toElem (ThirteenOf21 x) = toElem x
    toElem (FourteenOf21 x) = toElem x
    toElem (FifteenOf21 x) = toElem x
    toElem (SixteenOf21 x) = toElem x
    toElem (SeventeenOf21 x) = toElem x
    toElem (EighteenOf21 x) = toElem x
    toElem (NineteenOf21 x) = toElem x
    toElem (TwentyOf21 x) = toElem x
    toElem (TwentyOneOf21 x) = toElem x

----
data OneOf22 a b c d e f g h i j k l m n o p q r s t u v
    = OneOf22 a | TwoOf22 b | ThreeOf22 c | FourOf22 d | FiveOf22 e
    | SixOf22 f | SevenOf22 g | EightOf22 h | NineOf22 i | TenOf22 j
    | ElevenOf22 k | TwelveOf22 l | ThirteenOf22 m | FourteenOf22 n
    | FifteenOf22 o | SixteenOf22 p | SeventeenOf22 q | EighteenOf22 r
    | NineteenOf22 s | TwentyOf22 t | TwentyOneOf22 u | TwentyTwoOf22 v
    deriving (Eq,Show)

instance (XmlContent a,XmlContent b,XmlContent c,XmlContent d,XmlContent e
          ,XmlContent f,XmlContent g,XmlContent h,XmlContent i,XmlContent j
          ,XmlContent k,XmlContent l,XmlContent m,XmlContent n,XmlContent o
          ,XmlContent p,XmlContent q,XmlContent r,XmlContent s,XmlContent t
	  ,XmlContent u,XmlContent v)
    => XmlContent (OneOf22 a b c d e f g h i j k l m n o p q r s t u v)
  where
    fromElem cs =
        (choice OneOf22 $ choice TwoOf22 $ choice ThreeOf22 $ choice FourOf22
        $ choice FiveOf22 $ choice SixOf22 $ choice SevenOf22
        $ choice EightOf22 $ choice NineOf22 $ choice TenOf22
        $ choice ElevenOf22 $ choice TwelveOf22 $ choice ThirteenOf22
        $ choice FourteenOf22 $ choice FifteenOf22 $ choice SixteenOf22
        $ choice SeventeenOf22 $ choice EighteenOf22 $ choice NineteenOf22
        $ choice TwentyOf22 $ choice TwentyOneOf22 $ choice TwentyTwoOf22
        $ (\c->(Nothing,c))) cs
    toElem (OneOf22 x) = toElem x
    toElem (TwoOf22 x) = toElem x
    toElem (ThreeOf22 x) = toElem x
    toElem (FourOf22 x) = toElem x
    toElem (FiveOf22 x) = toElem x
    toElem (SixOf22 x) = toElem x
    toElem (SevenOf22 x) = toElem x
    toElem (EightOf22 x) = toElem x
    toElem (NineOf22 x) = toElem x
    toElem (TenOf22 x) = toElem x
    toElem (ElevenOf22 x) = toElem x
    toElem (TwelveOf22 x) = toElem x
    toElem (ThirteenOf22 x) = toElem x
    toElem (FourteenOf22 x) = toElem x
    toElem (FifteenOf22 x) = toElem x
    toElem (SixteenOf22 x) = toElem x
    toElem (SeventeenOf22 x) = toElem x
    toElem (EighteenOf22 x) = toElem x
    toElem (NineteenOf22 x) = toElem x
    toElem (TwentyOf22 x) = toElem x
    toElem (TwentyOneOf22 x) = toElem x
    toElem (TwentyTwoOf22 x) = toElem x

----
data OneOf23 a b c d e f g h i j k l m n o p q r s t u v w
    = OneOf23 a | TwoOf23 b | ThreeOf23 c | FourOf23 d | FiveOf23 e
    | SixOf23 f | SevenOf23 g | EightOf23 h | NineOf23 i | TenOf23 j
    | ElevenOf23 k | TwelveOf23 l | ThirteenOf23 m | FourteenOf23 n
    | FifteenOf23 o | SixteenOf23 p | SeventeenOf23 q | EighteenOf23 r
    | NineteenOf23 s | TwentyOf23 t | TwentyOneOf23 u | TwentyTwoOf23 v
    | TwentyThreeOf23 w
    deriving (Eq,Show)

instance (XmlContent a,XmlContent b,XmlContent c,XmlContent d,XmlContent e
          ,XmlContent f,XmlContent g,XmlContent h,XmlContent i,XmlContent j
          ,XmlContent k,XmlContent l,XmlContent m,XmlContent n,XmlContent o
          ,XmlContent p,XmlContent q,XmlContent r,XmlContent s,XmlContent t
	  ,XmlContent u,XmlContent v,XmlContent w)
    => XmlContent (OneOf23 a b c d e f g h i j k l m n o p q r s t u v w)
  where
    fromElem cs =
        (choice OneOf23 $ choice TwoOf23 $ choice ThreeOf23 $ choice FourOf23
        $ choice FiveOf23 $ choice SixOf23 $ choice SevenOf23
        $ choice EightOf23 $ choice NineOf23 $ choice TenOf23
        $ choice ElevenOf23 $ choice TwelveOf23 $ choice ThirteenOf23
        $ choice FourteenOf23 $ choice FifteenOf23 $ choice SixteenOf23
        $ choice SeventeenOf23 $ choice EighteenOf23 $ choice NineteenOf23
        $ choice TwentyOf23 $ choice TwentyOneOf23 $ choice TwentyTwoOf23
	$ choice TwentyThreeOf23
        $ (\c->(Nothing,c))) cs
    toElem (OneOf23 x) = toElem x
    toElem (TwoOf23 x) = toElem x
    toElem (ThreeOf23 x) = toElem x
    toElem (FourOf23 x) = toElem x
    toElem (FiveOf23 x) = toElem x
    toElem (SixOf23 x) = toElem x
    toElem (SevenOf23 x) = toElem x
    toElem (EightOf23 x) = toElem x
    toElem (NineOf23 x) = toElem x
    toElem (TenOf23 x) = toElem x
    toElem (ElevenOf23 x) = toElem x
    toElem (TwelveOf23 x) = toElem x
    toElem (ThirteenOf23 x) = toElem x
    toElem (FourteenOf23 x) = toElem x
    toElem (FifteenOf23 x) = toElem x
    toElem (SixteenOf23 x) = toElem x
    toElem (SeventeenOf23 x) = toElem x
    toElem (EighteenOf23 x) = toElem x
    toElem (NineteenOf23 x) = toElem x
    toElem (TwentyOf23 x) = toElem x
    toElem (TwentyOneOf23 x) = toElem x
    toElem (TwentyTwoOf23 x) = toElem x
    toElem (TwentyThreeOf23 x) = toElem x

----
data OneOf24 a b c d e f g h i j k l m n o p q r s t u v w x
    = OneOf24 a | TwoOf24 b | ThreeOf24 c | FourOf24 d | FiveOf24 e
    | SixOf24 f | SevenOf24 g | EightOf24 h | NineOf24 i | TenOf24 j
    | ElevenOf24 k | TwelveOf24 l | ThirteenOf24 m | FourteenOf24 n
    | FifteenOf24 o | SixteenOf24 p | SeventeenOf24 q | EighteenOf24 r
    | NineteenOf24 s | TwentyOf24 t | TwentyOneOf24 u | TwentyTwoOf24 v
    | TwentyThreeOf24 w | TwentyFourOf24 x
    deriving (Eq,Show)

instance (XmlContent a,XmlContent b,XmlContent c,XmlContent d,XmlContent e
          ,XmlContent f,XmlContent g,XmlContent h,XmlContent i,XmlContent j
          ,XmlContent k,XmlContent l,XmlContent m,XmlContent n,XmlContent o
          ,XmlContent p,XmlContent q,XmlContent r,XmlContent s,XmlContent t
	  ,XmlContent u,XmlContent v,XmlContent w,XmlContent x)
    => XmlContent (OneOf24 a b c d e f g h i j k l m n o p q r s t u v w x)
  where
    fromElem cs =
        (choice OneOf24 $ choice TwoOf24 $ choice ThreeOf24 $ choice FourOf24
        $ choice FiveOf24 $ choice SixOf24 $ choice SevenOf24
        $ choice EightOf24 $ choice NineOf24 $ choice TenOf24
        $ choice ElevenOf24 $ choice TwelveOf24 $ choice ThirteenOf24
        $ choice FourteenOf24 $ choice FifteenOf24 $ choice SixteenOf24
        $ choice SeventeenOf24 $ choice EighteenOf24 $ choice NineteenOf24
        $ choice TwentyOf24 $ choice TwentyOneOf24 $ choice TwentyTwoOf24
	$ choice TwentyThreeOf24 $ choice TwentyFourOf24
        $ (\c->(Nothing,c))) cs
    toElem (OneOf24 x) = toElem x
    toElem (TwoOf24 x) = toElem x
    toElem (ThreeOf24 x) = toElem x
    toElem (FourOf24 x) = toElem x
    toElem (FiveOf24 x) = toElem x
    toElem (SixOf24 x) = toElem x
    toElem (SevenOf24 x) = toElem x
    toElem (EightOf24 x) = toElem x
    toElem (NineOf24 x) = toElem x
    toElem (TenOf24 x) = toElem x
    toElem (ElevenOf24 x) = toElem x
    toElem (TwelveOf24 x) = toElem x
    toElem (ThirteenOf24 x) = toElem x
    toElem (FourteenOf24 x) = toElem x
    toElem (FifteenOf24 x) = toElem x
    toElem (SixteenOf24 x) = toElem x
    toElem (SeventeenOf24 x) = toElem x
    toElem (EighteenOf24 x) = toElem x
    toElem (NineteenOf24 x) = toElem x
    toElem (TwentyOf24 x) = toElem x
    toElem (TwentyOneOf24 x) = toElem x
    toElem (TwentyTwoOf24 x) = toElem x
    toElem (TwentyThreeOf24 x) = toElem x
    toElem (TwentyFourOf24 x) = toElem x


