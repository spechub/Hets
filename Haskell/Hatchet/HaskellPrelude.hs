{-------------------------------------------------------------------------------

        Copyright:              Mark Jones and The Hatchet Team 
                                (see file Contributors)

        Module:                 HaskellPrelude

        Description:            Hard coded definitions of types and classes
                                and type signatures of entities in the
                                Haskell Prelude.

                                When Hatchet supports multi-modules properly
                                much of this code will hopefull disappear.

                                The main tasks implemented by this module are:

        Primary Authors:        Mark Jones, Bernie Pope, Bryn Humberstone

        Notes:                  See the file License for license information

                                Large parts of this module were derived from
                                the work of Mark Jones' "Typing Haskell in
                                Haskell", (http://www.cse.ogi.edu/~mpj/thih/)

-------------------------------------------------------------------------------}

module HaskellPrelude where

import Representation  (Type (..),
                        Tyvar (..),
                        Tycon (..), 
                        Kind (..),
                        Qual (..),
                        Pred (..),
                        Class,
                        Inst,
                        Scheme (..),
                        Assump (..))

import AnnotatedHsSyn    -- almost everything

import Type             (inst)

--------------------------------------------------------------------------------

preludeInfixDecls :: [AHsDecl]
preludeInfixDecls
    = [9 `toRight` [sym "."], 
       9 `toLeft` [sym "!!"],
       8 `toRight` [sym "^", sym "^^", sym "**"], 
       7 `toLeft`  [sym "*", sym "/", sym "*", ident "quot", ident "rem", 
                    ident "div", ident "mod", sym ":%", sym "%"],
       6 `toLeft` [sym "+", sym "-"],
       5 `toRight` [sym "++", sym ":"], 
       4 `noSide`  [sym "==", sym "/=", sym "<", sym "<=",
                   sym ">=", sym ">", ident "elem", ident "notElem"],
       3 `toRight` [sym "&&"],
       2 `toRight` [sym "||"],
       1 `toLeft`  [sym ">>", sym ">>="],
       1 `toRight` [sym "=<<"],
       0 `toRight` [sym "$", sym "$!", ident "seq"]]
   where 
   sym name = AQual (AModule "Prelude") (AHsSymbol name)
   ident name = AQual (AModule "Prelude") (AHsIdent name)
   makeDecl assoc bind ahsnames = AHsInfixDecl bogusASrcLoc assoc bind ahsnames
   toRight = makeDecl AHsAssocRight
   toLeft = makeDecl AHsAssocLeft
   noSide = makeDecl AHsAssocNone
                   

-- this bit is an addition by Bryn (Feb 9 2002)
tyconsMembersHaskellPrelude :: [(AHsName, [AHsName])]
tyconsMembersHaskellPrelude
    = ["Bool"     <== ["True", "False"],
       "Maybe"    <== ["Nothing", "Just"],
       "Either"   <== ["Left", "Right"],
       "Ordering" <== ["LT", "EQ", "GT"],
       "()"       <=# ["()"],  
       "[]"       <=* [":"]
      ] 
    where
    qual name = AQual (AModule "Prelude") (AHsIdent name)
    qualsym name = AQual (AModule "Prelude") (AHsSymbol name)
    qualspec name = AQual (AModule "Prelude") (AHsSpecial name)
    tycon <== datacons = (qual tycon, map qual datacons)
    tycon <=* datacons = (qual tycon, map qualsym datacons)
    tycon <=# datacons = (qualspec tycon, map qualspec datacons)

infixr      4 `fn`
fn         :: Type -> Type -> Type
a `fn` b    = TArrow a b

-- built in type representations:

tChar      = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Char")) Star)
tList
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "[]")) (Kfun Star Star))
tUnit
 = TCon (Tycon (AQual (AModule "Prelude") (AHsSpecial "()")) Star)


preludeDefs
 =  [(AQual (AModule "Prelude") (AHsIdent "flip")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 2) `fn` TGen 1 `fn` TGen 0 `fn` TGen 2)),
     (AQual (AModule "Prelude") (AHsIdent "subtract")) :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "gcd")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "lcm")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "otherwise")) :>:
       Forall []
	 ([] :=>
	    tBool),
     (AQual (AModule "Prelude") (AHsSymbol "^")) :>:
       Forall [Star, Star]
	 ([isIn1 cNum (TGen 0), isIn1 cIntegral (TGen 1)] :=>
	    (TGen 0 `fn` TGen 1 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsSymbol "^^")) :>:
       Forall [Star, Star]
	 ([isIn1 cFractional (TGen 0), isIn1 cIntegral (TGen 1)] :=>
	    (TGen 0 `fn` TGen 1 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsSymbol ".")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1) `fn` (TGen 2 `fn` TGen 0) `fn` TGen 2 `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "fromIntegral")) :>:
       Forall [Star, Star]
	 ([isIn1 cIntegral (TGen 0), isIn1 cNum (TGen 1)] :=>
	    (TGen 0 `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "realToFrac")) :>:
       Forall [Star, Star]
	 ([isIn1 cReal (TGen 0), isIn1 cFractional (TGen 1)] :=>
	    (TGen 0 `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "sequence")) :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (TAp tList (TAp (TGen 0) (TGen 1)) `fn` TAp (TGen 0) (TAp tList (TGen 1)))),
     (AQual (AModule "Prelude") (AHsIdent "foldr")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 1) `fn` TGen 1 `fn` TAp tList (TGen 0) `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "sequence_")) :>:
       Forall [Kfun Star Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    (TAp tList (TAp (TGen 0) (TGen 1)) `fn` TAp (TGen 0) tUnit)),
     (AQual (AModule "Prelude") (AHsIdent "map")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 1))),
     (AQual (AModule "Prelude") (AHsIdent "mapM")) :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 `fn` TAp (TGen 0) (TGen 2)) `fn` TAp tList (TGen 1) `fn` TAp (TGen 0) (TAp tList (TGen 2)))),
     (AQual (AModule "Prelude") (AHsIdent "mapM_")) :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 `fn` TAp (TGen 0) (TGen 2)) `fn` TAp tList (TGen 1) `fn` TAp (TGen 0) tUnit)),
     (AQual (AModule "Prelude") (AHsSymbol "=<<")) :>:
       Forall [Kfun Star Star, Star, Star]
	 ([isIn1 cMonad (TGen 0)] :=>
	    ((TGen 1 `fn` TAp (TGen 0) (TGen 2)) `fn` TAp (TGen 0) (TGen 1) `fn` TAp (TGen 0) (TGen 2))),
     (AQual (AModule "Prelude") (AHsSymbol "&&")) :>:
       Forall []
	 ([] :=>
	    (tBool `fn` tBool `fn` tBool)),
     (AQual (AModule "Prelude") (AHsSymbol "||")) :>:
       Forall []
	 ([] :=>
	    (tBool `fn` tBool `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "not")) :>:
       Forall []
	 ([] :=>
	    (tBool `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isAscii")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isControl")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isPrint")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isSpace")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isUpper")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isLower")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isAlpha")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isDigit")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isAlphaNum")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "digitToInt")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tInt)),
     (AQual (AModule "Prelude") (AHsIdent "intToDigit")) :>:
       Forall []
	 ([] :=>
	    (tInt `fn` tChar)),
     (AQual (AModule "Prelude") (AHsIdent "toUpper")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tChar)),
     (AQual (AModule "Prelude") (AHsIdent "toLower")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tChar)),
     (AQual (AModule "Prelude") (AHsIdent "ord")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tInt)),
     (AQual (AModule "Prelude") (AHsIdent "chr")) :>:
       Forall []
	 ([] :=>
	    (tInt `fn` tChar)),
     (AQual (AModule "Prelude") (AHsIdent "maybe")) :>:
       Forall [Star, Star]
	 ([] :=>
	    (TGen 0 `fn` (TGen 1 `fn` TGen 0) `fn` TAp tMaybe (TGen 1) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "either")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1) `fn` (TGen 2 `fn` TGen 1) `fn` TAp (TAp tEither (TGen 0)) (TGen 2) `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "absReal")) :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0), isIn1 cOrd (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "signumReal")) :>:
       Forall [Star, Star]
	 ([isIn1 cOrd (TGen 0), isIn1 cNum (TGen 1),
	   isIn1 cNum (TGen 0)] :=>
	    (TGen 0 `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "numericEnumFrom")) :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "iterate")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 0) `fn` TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "numericEnumFromThen")) :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "takeWhile")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "numericEnumFromTo")) :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "numericEnumFromThenTo")) :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "reduce")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TAp tRatio (TGen 0))),
     (AQual (AModule "Prelude") (AHsSymbol "%")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TAp tRatio (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "realFloatToRational")) :>:
       Forall [Star]
	 ([isIn1 cRealFloat (TGen 0)] :=>
	    (TGen 0 `fn` TAp tRatio tInteger)),
     (AQual (AModule "Prelude") (AHsIdent "floatToRational")) :>:
       Forall []
	 ([] :=>
	    (tFloat `fn` TAp tRatio tInteger)),
     (AQual (AModule "Prelude") (AHsIdent "doubleToRational")) :>:
       Forall []
	 ([] :=>
	    (tDouble `fn` TAp tRatio tInteger)),
     (AQual (AModule "Prelude") (AHsIdent "const")) :>:
       Forall [Star, Star]
	 ([] :=>
	    (TGen 0 `fn` TGen 1 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "asTypeOf")) :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 `fn` TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "numerator")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tRatio (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "denominator")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tRatio (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "rationalToRealFloat")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tRatio tInteger `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "rationalToFloat")) :>:
       Forall []
	 ([] :=>
	    (TAp tRatio tInteger `fn` tFloat)),
     (AQual (AModule "Prelude") (AHsIdent "rationalToDouble")) :>:
       Forall []
	 ([] :=>
	    (TAp tRatio tInteger `fn` tDouble)),
     (AQual (AModule "Prelude") (AHsIdent "floatProperFraction")) :>:
       Forall [Star, Star, Star]
	 ([isIn1 cRealFloat (TGen 0), isIn1 cNum (TGen 1),
	   isIn1 cRealFloat (TGen 2)] :=>
	    (TGen 2 `fn` TTuple [TGen 1, TGen 0])),
     (AQual (AModule "Prelude") (AHsIdent "fst")) :>:
       Forall [Star, Star]
	 ([] :=>
	    (TTuple [TGen 0, TGen 1] `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "snd")) :>:
       Forall [Star, Star]
	 ([] :=> (TTuple [TGen 0, TGen 1] `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "curry")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TTuple [TGen 0, TGen 1] `fn` TGen 2) `fn` TGen 0 `fn` TGen 1 `fn` TGen 2)),
     (AQual (AModule "Prelude") (AHsIdent "uncurry")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 2) `fn` TTuple [TGen 0, TGen 1] `fn` TGen 2)),
     (AQual (AModule "Prelude") (AHsIdent "id")) :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsSymbol "$")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1) `fn` TGen 0 `fn` TGen 1)),
     (AQual (AModule "Prelude") (AHsIdent "until")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` (TGen 0 `fn` TGen 0) `fn` TGen 0 `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "undefined")) :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "intToRatio")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (tInt `fn` TAp tRatio (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "doubleToRatio")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (tDouble `fn` TAp tRatio (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "approxRational")) :>:
       Forall [Star]
	 ([isIn1 cRealFrac (TGen 0)] :=>
	    (TGen 0 `fn` TGen 0 `fn` TAp tRatio tInteger)),
     (AQual (AModule "Prelude") (AHsIdent "head")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "last")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "tail")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "init")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "null")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` tBool)),
     (AQual (AModule "Prelude") (AHsSymbol "++")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "filter")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "concat")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TAp tList (TGen 0)) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "foldl'")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 0) `fn` TGen 0 `fn` TAp tList (TGen 1) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "length")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` tInt)),
     (AQual (AModule "Prelude") (AHsSymbol "!!")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` tInt `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "foldl")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 0) `fn` TGen 0 `fn` TAp tList (TGen 1) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "foldl1")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 0 `fn` TGen 0) `fn` TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "scanl")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 0) `fn` TGen 0 `fn` TAp tList (TGen 1) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "scanl1")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 0 `fn` TGen 0) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "foldr1")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 0 `fn` TGen 0) `fn` TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "scanr")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 1) `fn` TGen 1 `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 1))),
     (AQual (AModule "Prelude") (AHsIdent "scanr1")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 0 `fn` TGen 0) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "repeat")) :>:
       Forall [Star]
	 ([] :=>
	    (TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "take")) :>:
       Forall [Star]
	 ([] :=>
	    (tInt `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "replicate")) :>:
       Forall [Star]
	 ([] :=>
	    (tInt `fn` TGen 0 `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "cycle")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "drop")) :>:
       Forall [Star]
	 ([] :=>
	    (tInt `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "splitAt")) :>:
       Forall [Star]
	 ([] :=>
	    (tInt `fn` TAp tList (TGen 0) `fn` TTuple [TAp tList (TGen 0), TAp tList (TGen 0)])),
     (AQual (AModule "Prelude") (AHsIdent "dropWhile")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "span")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` TTuple [TAp tList (TGen 0), TAp tList (TGen 0)])),
     (AQual (AModule "Prelude") (AHsIdent "break")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` TTuple [TAp tList (TGen 0), TAp tList (TGen 0)])),
     (AQual (AModule "Prelude") (AHsIdent "lines")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList (TAp tList tChar))),
     (AQual (AModule "Prelude") (AHsIdent "words")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList (TAp tList tChar))),
     (AQual (AModule "Prelude") (AHsIdent "concatMap")) :>:
       Forall [Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TAp tList (TGen 1)) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 1))),
     (AQual (AModule "Prelude") (AHsIdent "unlines")) :>:
       Forall []
	 ([] :=>
	    (TAp tList (TAp tList tChar) `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "unwords")) :>:
       Forall []
	 ([] :=>
	    (TAp tList (TAp tList tChar) `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "reverse")) :>:
       Forall [Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "and")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tBool `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "or")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tBool `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "any")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "all")) :>:
       Forall [Star]
	 ([] :=>
	    ((TGen 0 `fn` tBool) `fn` TAp tList (TGen 0) `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "elem")) :>:
       Forall [Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TGen 0 `fn` TAp tList (TGen 0) `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "notElem")) :>:
       Forall [Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TGen 0 `fn` TAp tList (TGen 0) `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "lookup")) :>:
       Forall [Star, Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TGen 0 `fn` TAp tList (TTuple [TGen 0, TGen 1]) `fn` TAp tMaybe (TGen 1))),
     (AQual (AModule "Prelude") (AHsIdent "sum")) :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0)] :=>
	    (TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "product")) :>:
       Forall [Star]
	 ([isIn1 cNum (TGen 0)] :=>
	    (TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "maximum")) :>:
       Forall [Star]
	 ([isIn1 cOrd (TGen 0)] :=>
	    (TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "minimum")) :>:
       Forall [Star]
	 ([isIn1 cOrd (TGen 0)] :=>
	    (TAp tList (TGen 0) `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "zipWith")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 2) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 1) `fn` TAp tList (TGen 2))),
     (AQual (AModule "Prelude") (AHsIdent "zip")) :>:
       Forall [Star, Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 1) `fn` TAp tList (TTuple [TGen 0, TGen 1]))),
     (AQual (AModule "Prelude") (AHsIdent "zipWith3")) :>:
       Forall [Star, Star, Star, Star]
	 ([] :=>
	    ((TGen 0 `fn` TGen 1 `fn` TGen 2 `fn` TGen 3) `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 1) `fn` TAp tList (TGen 2) `fn` TAp tList (TGen 3))),
     (AQual (AModule "Prelude") (AHsIdent "zip3")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 1) `fn` TAp tList (TGen 2) `fn` TAp tList (TTuple [TGen 0, TGen 1, TGen 2]))),
     (AQual (AModule "Prelude") (AHsIdent "unzip")) :>:
       Forall [Star, Star]
	 ([] :=>
	    (TAp tList (TTuple [TGen 0, TGen 1]) `fn` TTuple [TAp tList (TGen 0), TAp tList (TGen 1)])),
     (AQual (AModule "Prelude") (AHsIdent "unzip3")) :>:
       Forall [Star, Star, Star]
	 ([] :=>
	    (TAp tList (TTuple [TGen 0, TGen 1, TGen 2]) `fn` TTuple [TAp tList (TGen 0), TAp tList (TGen 1), TAp tList (TGen 2)])),
     (AQual (AModule "Prelude") (AHsIdent "reads")) :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "shows")) :>:
       Forall [Star]
	 ([isIn1 cShow (TGen 0)] :=>
	    (TGen 0 `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "nonnull")) :>:
       Forall []
	 ([] :=>
	    ((tChar `fn` tBool) `fn` TAp tList tChar `fn` TAp tList (TTuple [TAp tList tChar, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "lexDigits")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TAp tList tChar, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "lexmatch")) :>:
       Forall [Star]
	 ([isIn1 cEq (TGen 0)] :=>
	    (TAp tList (TGen 0) `fn` TAp tList (TGen 0) `fn` TTuple [TAp tList (TGen 0), TAp tList (TGen 0)])),
     (AQual (AModule "Prelude") (AHsIdent "asciiTab")) :>:
       Forall []
	 ([] :=>
	    (TAp tList (TTuple [tChar, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "lexLitChar")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TAp tList tChar, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "lex")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TAp tList tChar, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "read")) :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "showChar")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "showString")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "showParen")) :>:
       Forall []
	 ([] :=>
	    (tBool `fn` (TAp tList tChar `fn` TAp tList tChar) `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "showField")) :>:
       Forall [Star]
	 ([isIn1 cShow (TGen 0)] :=>
	    (TAp tList tChar `fn` TGen 0 `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "readParen")) :>:
       Forall [Star]
	 ([] :=>
	    (tBool `fn` (TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar])) `fn` TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "readField")) :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "isOctDigit")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "isHexDigit")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` tBool)),
     (AQual (AModule "Prelude") (AHsIdent "readInt")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 `fn` (tChar `fn` tBool) `fn` (tChar `fn` tInt) `fn` TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "readHex")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "readOct")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "readDec")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "readLitChar")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [tChar, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "protectEsc")) :>:
       Forall [Star]
	 ([] :=>
	    ((tChar `fn` tBool) `fn` (TAp tList tChar `fn` TGen 0) `fn` TAp tList tChar `fn` TGen 0)),
     (AQual (AModule "Prelude") (AHsIdent "showLitChar")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "showInt")) :>:
       Forall [Star]
	 ([isIn1 cIntegral (TGen 0)] :=>
	    (TGen 0 `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "readSigned")) :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    ((TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar])) `fn` TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "showSigned")) :>:
       Forall [Star]
	 ([isIn1 cReal (TGen 0)] :=>
	    ((TGen 0 `fn` TAp tList tChar `fn` TAp tList tChar) `fn` tInt `fn` TGen 0 `fn` TAp tList tChar `fn` TAp tList tChar)),
     (AQual (AModule "Prelude") (AHsIdent "readFloat")) :>:
       Forall [Star]
	 ([isIn1 cRealFloat (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tList (TTuple [TGen 0, TAp tList tChar]))),
     (AQual (AModule "Prelude") (AHsIdent "putStrLn")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tIO tUnit)),
     (AQual (AModule "Prelude") (AHsIdent "print")) :>:
       Forall [Star]
	 ([isIn1 cShow (TGen 0)] :=>
	    (TGen 0 `fn` TAp tIO tUnit)),
     (AQual (AModule "Prelude") (AHsIdent "getLine")) :>:
       Forall []
	 ([] :=>
	    (TAp tIO (TAp tList tChar))),
     (AQual (AModule "Prelude") (AHsIdent "readIO")) :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tList tChar `fn` TAp tIO (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "readLn")) :>:
       Forall [Star]
	 ([isIn1 cRead (TGen 0)] :=>
	    (TAp tIO (TGen 0))),
     (AQual (AModule "Prelude") (AHsIdent "interact")) :>:
       Forall []
	 ([] :=>
	    ((TAp tList tChar `fn` TAp tList tChar) `fn` TAp tIO tUnit)),
     (AQual (AModule "Prelude") (AHsIdent "return")) :>: (Forall [Kfun Star Star, Star]
                  ([isIn1 cMonad (TGen 0)] :=>
                   (TGen 1 `fn` TAp (TGen 0) (TGen 1)))),
 
     (AQual (AModule "Prelude") (AHsIdent "mod")) :>: 
        Forall [Star]
         ([isIn1 cIntegral (TGen 0)] :=>
            (TGen 0 `fn` TGen 0 `fn` TGen 0)),

     (AQual (AModule "Prelude") (AHsIdent "div")) :>:
        Forall [Star]
         ([isIn1 cIntegral (TGen 0)] :=>
            (TGen 0 `fn` TGen 0 `fn` TGen 0)),


     (AQual (AModule "Prelude") (AHsSymbol ">>=")) :>: (Forall [Kfun Star Star, Star, Star]
               ([isIn1 cMonad (TGen 0)] :=>
                (TAp (TGen 0) (TGen 1) `fn` (TGen 1 `fn` TAp (TGen 0) (TGen 2)) `fn` TAp (TGen 0) (TGen 2)))), 

     (AQual (AModule "Prelude") (AHsSymbol ">>")) :>: (Forall [Kfun Star Star, Star, Star]
              ([isIn1 cMonad (TGen 0)] :=>
               (TAp (TGen 0) (TGen 1) `fn` TAp (TGen 0) (TGen 2) `fn` TAp (TGen 0) (TGen 2)))), 

     (AQual (AModule "Prelude") (AHsIdent "max")) :>:
        Forall [Star]
           ([IsIn cOrd (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` TGen 0)),

     (AQual (AModule "Prelude") (AHsIdent "min")) :>:
        Forall [Star]
           ([IsIn cOrd (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` TGen 0)),

     (AQual (AModule "Prelude") (AHsIdent "round")) :>:
        Forall [Star, Star]
           ([IsIn cRealFrac (TGen 0), IsIn cIntegral (TGen 1)] :=>
              (TGen 0 `fn` TGen 1)),

     (AQual (AModule "Prelude") (AHsIdent "sqrt")) :>:
        Forall [Star]
           ([IsIn cFloating (TGen 0)] :=>
              (TGen 0 `fn` TGen 0)),

     (AQual (AModule "Prelude") (AHsIdent "fail")) :>: (Forall [Kfun Star Star, Star]
                ([isIn1 cMonad (TGen 0)] :=>
                 (tString `fn` TAp (TGen 0) (TGen 1)))), 

     (AQual (AModule "Prelude") (AHsIdent "show")) :>: 
        Forall [Star]
          ([IsIn cShow (TGen 0)] :=>
           (TGen 0 `fn` tString)),  

     (AQual (AModule "Prelude") (AHsIdent "putStr")) :>:
       Forall []
	 ([] :=>
	    (TAp tList tChar `fn` TAp tIO tUnit)),

     (AQual (AModule "Prelude") (AHsIdent "getChar")) :>:
       Forall []
	 ([] :=>
	    (TAp tIO tChar)),

     (AQual (AModule "Prelude") (AHsIdent "putChar")) :>:
       Forall []
	 ([] :=>
	    (tChar `fn` TAp tIO tUnit)),

     (AQual (AModule "Prelude") (AHsIdent "seq"))   :>:
       Forall [Star,Star]
          ([] :=>
            (TGen 0 `fn` TGen 1 `fn` TGen 1)),

     (AQual (AModule "Prelude") (AHsIdent "error")) :>:
       Forall [Star]
         ([] :=> (tString `fn` TGen 0)),

     (AQual (AModule "Prelude") (AHsIdent "compare")) :>: (Forall [Star]
                   ([isIn1 cOrd (TGen 0)] :=>
                    (TGen 0 `fn` TGen 0 `fn` tOrdering))),

     (AQual (AModule "Prelude") (AHsSymbol "<")) :>: (Forall [Star]
             ([isIn1 cOrd (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` tBool))),

     (AQual (AModule "Prelude") (AHsSymbol "<=")) :>: (Forall [Star]
              ([isIn1 cOrd (TGen 0)] :=>
               (TGen 0 `fn` TGen 0 `fn` tBool))),

     (AQual (AModule "Prelude") (AHsSymbol ">=")) :>: (Forall [Star]
              ([isIn1 cOrd (TGen 0)] :=>
               (TGen 0 `fn` TGen 0 `fn` tBool))),

     (AQual (AModule "Prelude") (AHsSymbol ">")) :>: (Forall [Star]
             ([isIn1 cOrd (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` tBool))),

     (AQual (AModule "Prelude") (AHsSymbol "==")) :>: (Forall [Star]
              ([isIn1 cEq (TGen 0)] :=>
               (TGen 0 `fn` TGen 0 `fn` tBool))),
     (AQual (AModule "Prelude") (AHsSymbol "/=")) :>: (Forall [Star]
              ([isIn1 cEq (TGen 0)] :=>
               (TGen 0 `fn` TGen 0 `fn` tBool))),
     (AQual (AModule "Prelude") (AHsSymbol "+")) :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` TGen 0))),
     (AQual (AModule "Prelude") (AHsSymbol "-")) :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` TGen 0))),
     (AQual (AModule "Prelude") (AHsSymbol "*")) :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=>
              (TGen 0 `fn` TGen 0 `fn` TGen 0)))]


preludeDataCons :: [Assump] 
preludeDataCons
      = [ consCfun, nilCfun, unitCfun, trueCfun, falseCfun, nothingCfun, justCfun, leftCfun, rightCfun ]


isIn1 c t    = IsIn c t

mkInst ks = inst ts 
 where ts   = zipWith (\v k -> TVar (Tyvar v k)) vars ks
       vars = [AUnQual $ AHsIdent $ [c] | c <-['a'..'z'] ] ++
              [AUnQual $  AHsIdent $ c : show n | n <-[0::Int ..], c<-['a'..'z'] ]

unitCfun
 = (AQual (AModule "Prelude") (AHsSpecial "()")) :>: (Forall []
              ([] :=> 
               tUnit))

nilCfun
 = (AQual (AModule "Prelude") (AHsIdent "[]")) :>: (Forall [Star]
              ([] :=> 
               (TAp tList (TGen 0))))

consCfun
 = (AQual (AModule "Prelude") (AHsSymbol ":")) :>: (Forall [Star]
             ([] :=> 
              (TGen 0 `fn` TAp tList (TGen 0) `fn` TAp tList (TGen 0))))

tReadS a
 = TAp tList tChar `fn` TAp tList (TTuple [a, TAp tList tChar])

tShowS
 = TAp tList tChar `fn` TAp tList tChar

tBool
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Bool")) Star)
falseCfun
 = (AQual (AModule "Prelude") (AHsIdent "False")) :>: (Forall []
                 ([] :=> 
                  tBool))
trueCfun
 = (AQual (AModule "Prelude") (AHsIdent "True")) :>: (Forall []
                ([] :=> 
                 tBool))

tString
 = TAp tList tChar

tMaybe
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Maybe")) (Kfun Star Star))
nothingCfun
 = (AQual (AModule "Prelude") (AHsIdent "Nothing")) :>: (Forall [Star]
                   ([] :=> 
                    (TAp tMaybe (TGen 0))))
justCfun
 = (AQual (AModule "Prelude") (AHsIdent "Just")) :>: (Forall [Star]
                ([] :=> 
                 (TGen 0 `fn` TAp tMaybe (TGen 0))))

tEither
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Either")) (Kfun Star (Kfun Star Star)))
leftCfun
 = (AQual (AModule "Prelude") (AHsIdent "Left")) :>: (Forall [Star, Star]
                ([] :=> 
                 (TGen 0 `fn` TAp (TAp tEither (TGen 0)) (TGen 1))))
rightCfun
 = (AQual (AModule "Prelude") (AHsIdent "Right")) :>: (Forall [Star, Star]
                 ([] :=> 
                  (TGen 1 `fn` TAp (TAp tEither (TGen 0)) (TGen 1))))

tOrdering
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Ordering")) Star)
lTCfun
 = (AQual (AModule "Prelude") (AHsIdent "LT")) :>: (Forall []
              ([] :=> 
               tOrdering))
eQCfun
 = (AQual (AModule "Prelude") (AHsIdent "EQ")) :>: (Forall []
              ([] :=> 
               tOrdering))
gTCfun
 = (AQual (AModule "Prelude") (AHsIdent "GT")) :>: (Forall []
              ([] :=> 
               tOrdering))

tInt
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Int")) Star)

tInteger
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Integer")) Star)

tFloat
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Float")) Star)

tDouble
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Double")) Star)

tRatio
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "Ratio")) (Kfun Star Star))
-- XXX -- surely :% should be a Symbol rather than Ident?
consratCfun
 = (AQual (AModule "Prelude") (AHsIdent ":%")) :>: (Forall [Star]
              ([isIn1 cIntegral (TGen 0)] :=> 
               (TGen 0 `fn` TGen 0 `fn` TAp tRatio (TGen 0))))

tRational
 = TAp tRatio tInteger

tIOError
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "IOError")) Star)

tFilePath
 = TAp tList tChar

tIO
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "IO")) (Kfun Star Star))
iOCfun
 = (AQual (AModule "Prelude") (AHsIdent "IO")) :>: (Forall [Star]
              ([] :=> 
               (((tIOError `fn` TAp tIOResult (TGen 0)) `fn` (TGen 0 `fn` TAp tIOResult (TGen 0)) `fn` TAp tIOResult (TGen 0)) `fn` TAp tIO (TGen 0))))

tIOResult
 = TCon (Tycon (AQual (AModule "Prelude") (AHsIdent "IOResult")) (Kfun Star Star))


tId
 = TAp tList tChar



cEq = (AQual (AModule "Prelude") (AHsIdent "Eq"))

cEqTriple = ((AQual (AModule "Prelude") (AHsIdent "Eq")), ([], instsEq, methodSigsEq))

eqMfun
 = (AQual (AModule "Prelude") (AHsIdent "==")) :>: (Forall [Star]
              ([isIn1 cEq (TGen 0)] :=> 
               (TGen 0 `fn` TGen 0 `fn` tBool)))
neqMfun
 = (AQual (AModule "Prelude") (AHsIdent "/=")) :>: (Forall [Star]
              ([isIn1 cEq (TGen 0)] :=> 
               (TGen 0 `fn` TGen 0 `fn` tBool)))

instsEq
 = [mkInst []
     ([] :=> 
      isIn1 cEq tUnit),
    mkInst []
     ([] :=> 
      isIn1 cEq tChar),
    mkInst [Star]
     ([isIn1 cEq (TGen 0)] :=> 
      isIn1 cEq (TAp tList (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cEq tInt),
    mkInst []
     ([] :=> 
      isIn1 cEq tInteger),
    mkInst []
     ([] :=> 
      isIn1 cEq tFloat),
    mkInst []
     ([] :=> 
      isIn1 cEq tDouble),
    mkInst []
     ([] :=> 
      isIn1 cEq tBool),
    mkInst [Star]
     ([isIn1 cEq (TGen 0)] :=> 
      isIn1 cEq (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1)] :=> 
      isIn1 cEq (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst []
     ([] :=> 
      isIn1 cEq tOrdering),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cEq (TAp tRatio (TGen 0))),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1),
       isIn1 cEq (TGen 2),
       isIn1 cEq (TGen 3),
       isIn1 cEq (TGen 4)] :=> 
      isIn1 cEq (TTuple [TGen 0, TGen 1, TGen 2, TGen 3, TGen 4])),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1),
       isIn1 cEq (TGen 2),
       isIn1 cEq (TGen 3)] :=> 
      isIn1 cEq (TTuple [TGen 0, TGen 1, TGen 2, TGen 3])),
    mkInst [Star, Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1),
       isIn1 cEq (TGen 2)] :=> 
      isIn1 cEq (TTuple [TGen 0, TGen 1, TGen 2])),
    mkInst [Star, Star]
     ([isIn1 cEq (TGen 0),
       isIn1 cEq (TGen 1)] :=> 
      isIn1 cEq (TTuple [TGen 0, TGen 1]))
    ]

-- methodSigsEq :: [A(AHsDecl)]
methodSigsEq 
   = [
      {-
      AAHsTypeSig bogusSrcLoc 
                [AUnQual "=="] 
                (AAHsAQualType [(AUnQual "Eq", AUnQual "a")]
                    (AAHsTyFun (AAHsTyVar (AUnQual "a")) (AAHsTyFun (AAHsTyVar (AUnQual "a")) (AAHsTyCon (AUnQual "Bool"))))),
      AAHsTypeSig bogusSrcLoc 
                [AUnQual "/="] 
                (AAHsAQualType [(AUnQual "Eq", AUnQual "a")]
                    (AAHsTyFun (AAHsTyVar (AUnQual "a")) (AAHsTyFun (AAHsTyVar (AUnQual "a")) (AAHsTyCon (AUnQual "Bool")))))
       -}
     ]

cOrd = AQual (AModule "Prelude") (AHsIdent "Ord")

cOrdTriple = ((AQual (AModule "Prelude") (AHsIdent "Ord")), ([cEq], instsOrd, methodSigsOrd))

compareMfun
 = (AQual (AModule "Prelude") (AHsIdent "compare")) :>: (Forall [Star]
                   ([isIn1 cOrd (TGen 0)] :=> 
                    (TGen 0 `fn` TGen 0 `fn` tOrdering)))
ltMfun
 = (AQual (AModule "Prelude") (AHsIdent "<")) :>: (Forall [Star]
             ([isIn1 cOrd (TGen 0)] :=> 
              (TGen 0 `fn` TGen 0 `fn` tBool)))
leMfun
 = (AQual (AModule "Prelude") (AHsIdent "<=")) :>: (Forall [Star]
              ([isIn1 cOrd (TGen 0)] :=> 
               (TGen 0 `fn` TGen 0 `fn` tBool)))
geMfun
 = (AQual (AModule "Prelude") (AHsIdent ">=")) :>: (Forall [Star]
              ([isIn1 cOrd (TGen 0)] :=> 
               (TGen 0 `fn` TGen 0 `fn` tBool)))
gtMfun
 = (AQual (AModule "Prelude") (AHsIdent ">")) :>: (Forall [Star]
             ([isIn1 cOrd (TGen 0)] :=> 
              (TGen 0 `fn` TGen 0 `fn` tBool)))
maxMfun
 = (AQual (AModule "Prelude") (AHsIdent "max")) :>: (Forall [Star]
               ([isIn1 cOrd (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0 `fn` TGen 0)))
minMfun
 = (AQual (AModule "Prelude") (AHsIdent "min")) :>: (Forall [Star]
               ([isIn1 cOrd (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0 `fn` TGen 0)))

instsOrd
 = [mkInst []
     ([] :=> 
      isIn1 cOrd tUnit),
    mkInst []
     ([] :=> 
      isIn1 cOrd tChar),
    mkInst [Star]
     ([isIn1 cOrd (TGen 0)] :=> 
      isIn1 cOrd (TAp tList (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cOrd tInt),
    mkInst []
     ([] :=> 
      isIn1 cOrd tInteger),
    mkInst []
     ([] :=> 
      isIn1 cOrd tFloat),
    mkInst []
     ([] :=> 
      isIn1 cOrd tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cOrd (TAp tRatio (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cOrd tBool),
    mkInst [Star]
     ([isIn1 cOrd (TGen 0)] :=> 
      isIn1 cOrd (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1)] :=> 
      isIn1 cOrd (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst []
     ([] :=> 
      isIn1 cOrd tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1),
       isIn1 cOrd (TGen 2),
       isIn1 cOrd (TGen 3),
       isIn1 cOrd (TGen 4)] :=> 
      isIn1 cOrd (TTuple [TGen 0, TGen 1, TGen 2, TGen 3, TGen 4])),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1),
       isIn1 cOrd (TGen 2),
       isIn1 cOrd (TGen 3)] :=> 
      isIn1 cOrd (TTuple [TGen 0, TGen 1, TGen 2, TGen 3])),
    mkInst [Star, Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1),
       isIn1 cOrd (TGen 2)] :=> 
      isIn1 cOrd (TTuple [TGen 0, TGen 1, TGen 2])),
    mkInst [Star, Star]
     ([isIn1 cOrd (TGen 0),
       isIn1 cOrd (TGen 1)] :=> 
      isIn1 cOrd (TTuple [TGen 0, TGen 1]))]

-- methodSigsOrd :: [(AHsDecl)]
methodSigsOrd 
   = [
       {-
       AHsTypeSig bogusSrcLoc 
          [AUnQual "compare"] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Ordering"))))),

       AHsTypeSig bogusSrcLoc 
          [AUnQual "<"] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool"))))),

       AHsTypeSig bogusSrcLoc 
          [AUnQual "<="] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool"))))),

       AHsTypeSig bogusSrcLoc 
          [AUnQual ">="] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool"))))),

       AHsTypeSig bogusSrcLoc 
          [AUnQual ">"] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool"))))),

       AHsTypeSig bogusSrcLoc
          [AUnQual "max"] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

       AHsTypeSig bogusSrcLoc
          [AUnQual "min"] 
             (AHsAQualType [(AUnQual "Ord", AUnQual "a")]
                (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))))
    
      -}
     ]

cBounded = (AQual (AModule "Prelude") (AHsIdent "Bounded"))
cBoundedTriple = ((AQual (AModule "Prelude") (AHsIdent "Bounded")), ([], instsBounded, methodSigsBounded))

minBoundMfun
 = (AQual (AModule "Prelude") (AHsIdent "minBound")) :>: (Forall [Star]
                    ([isIn1 cBounded (TGen 0)] :=> 
                     (TGen 0)))
maxBoundMfun
 = (AQual (AModule "Prelude") (AHsIdent "maxBound")) :>: (Forall [Star]
                    ([isIn1 cBounded (TGen 0)] :=> 
                     (TGen 0)))

instsBounded
 = [mkInst []
     ([] :=> 
      isIn1 cBounded tUnit),
    mkInst []
     ([] :=> 
      isIn1 cBounded tChar),
    mkInst []
     ([] :=> 
      isIn1 cBounded tInt),
    mkInst []
     ([] :=> 
      isIn1 cBounded tBool),
    mkInst []
     ([] :=> 
      isIn1 cBounded tOrdering)]

-- methodSigsBounded :: [(AHsDecl)]
methodSigsBounded 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "minBound"] 
               (AHsAQualType [(AUnQual "Bounded", AUnQual "a")]
                  (AHsTyVar (AUnQual "a"))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "maxBound"] 
               (AHsAQualType [(AUnQual "Bounded", AUnQual "a")]
                  (AHsTyVar (AUnQual "a")))
      -}

     ]

{-
cNum = Class { name = "Num",
               super = [cEq, cShow],
               insts = instsNum }
-}
cNum = AQual (AModule "Prelude") (AHsIdent "Num")
cNumTriple = ((AQual (AModule "Prelude") (AHsIdent "Num")), ([cEq, cShow], instsNum, methodSigsNum))

plusMfun
 = (AQual (AModule "Prelude") (AHsIdent "+")) :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=> 
              (TGen 0 `fn` TGen 0 `fn` TGen 0)))
minusMfun
 = (AQual (AModule "Prelude") (AHsIdent "-")) :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=> 
              (TGen 0 `fn` TGen 0 `fn` TGen 0)))
timesMfun
 = (AQual (AModule "Prelude") (AHsIdent "*")) :>: (Forall [Star]
             ([isIn1 cNum (TGen 0)] :=> 
              (TGen 0 `fn` TGen 0 `fn` TGen 0)))
negateMfun
 = (AQual (AModule "Prelude") (AHsIdent "negate")) :>: (Forall [Star]
                  ([isIn1 cNum (TGen 0)] :=> 
                   (TGen 0 `fn` TGen 0)))
absMfun
 = (AQual (AModule "Prelude") (AHsIdent "abs")) :>: (Forall [Star]
               ([isIn1 cNum (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0)))
signumMfun
 = (AQual (AModule "Prelude") (AHsIdent "signum")) :>: (Forall [Star]
                  ([isIn1 cNum (TGen 0)] :=> 
                   (TGen 0 `fn` TGen 0)))
fromIntegerMfun
 = (AQual (AModule "Prelude") (AHsIdent "fromInteger")) :>: (Forall [Star]
                       ([isIn1 cNum (TGen 0)] :=> 
                        (tInteger `fn` TGen 0)))
fromIntMfun
 = (AQual (AModule "Prelude") (AHsIdent "fromInt")) :>: (Forall [Star]
                   ([isIn1 cNum (TGen 0)] :=> 
                    (tInt `fn` TGen 0)))

instsNum
 = [mkInst []
     ([] :=> 
      isIn1 cNum tInt),
    mkInst []
     ([] :=> 
      isIn1 cNum tInteger),
    mkInst []
     ([] :=> 
      isIn1 cNum tFloat),
    mkInst []
     ([] :=> 
      isIn1 cNum tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cNum (TAp tRatio (TGen 0)))]

-- methodSigsNum :: [(AHsDecl)]
methodSigsNum 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "+"] 
               (AHsAQualType [(AUnQual "Num", AUnQual "a")] 
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "-"] 
               (AHsAQualType [(AUnQual "Num", AUnQual "a")] 
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "*"] 
               (AHsAQualType [(AUnQual "Num", AUnQual "a")] 
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "negate"] 
               (AHsAQualType [(AUnQual "Num", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "abs"] 
               (AHsAQualType [(AUnQual "Num", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "signum"] 
               (AHsAQualType [(AUnQual "Num", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),


      AHsTypeSig bogusSrcLoc 
         [AUnQual "fromInteger"] 
            (AHsAQualType [(AUnQual "Num", AUnQual "a")]
               (AHsTyFun (AHsTyCon (AUnQual "Integer")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig bogusSrcLoc
         [AUnQual "fromInt"] 
            (AHsAQualType [(AUnQual "Num", AUnQual "a")]
               (AHsTyFun (AHsTyCon (AUnQual "Int")) (AHsTyVar (AUnQual "a"))))

        -}
     ]

cReal = AQual (AModule "Prelude") (AHsIdent "Real")
cRealTriple = ((AQual (AModule "Prelude") (AHsIdent "Real")), ([cNum, cOrd], instsReal, methodSigsReal))

toRationalMfun
 = (AQual (AModule "Prelude") (AHsIdent "toRational")) :>: (Forall [Star]
                      ([isIn1 cReal (TGen 0)] :=> 
                       (TGen 0 `fn` tRational)))

instsReal
 = [mkInst []
     ([] :=> 
      isIn1 cReal tInt),
    mkInst []
     ([] :=> 
      isIn1 cReal tInteger),
    mkInst []
     ([] :=> 
      isIn1 cReal tFloat),
    mkInst []
     ([] :=> 
      isIn1 cReal tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cReal (TAp tRatio (TGen 0)))]

-- methodSigsReal :: [(AHsDecl)]
methodSigsReal 
   = [
       {-
      AHsTypeSig bogusSrcLoc 
         [AUnQual "toRational"] 
            (AHsAQualType [(AUnQual "Real", AUnQual "a")]
               (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Rational"))))
       -}
     ]

{-
cIntegral = Class { name = "Integral",
                    super = [cReal, cEnum],
                    insts = instsIntegral }
-}
cIntegral = AQual (AModule "Prelude") (AHsIdent "Integral")
cIntegralTriple = ((AQual (AModule "Prelude") (AHsIdent "Integral")), ([cReal, cEnum], instsIntegral, methodSigsIntegral))

quotMfun
 = (AQual (AModule "Prelude") (AHsIdent "quot")) :>: (Forall [Star]
                ([isIn1 cIntegral (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0 `fn` TGen 0)))
remMfun
 = (AQual (AModule "Prelude") (AHsIdent "rem")) :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0 `fn` TGen 0)))
divMfun
 = (AQual (AModule "Prelude") (AHsIdent "div")) :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0 `fn` TGen 0)))
modMfun
 = (AQual (AModule "Prelude") (AHsIdent "mod")) :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0 `fn` TGen 0)))
quotRemMfun
 = (AQual (AModule "Prelude") (AHsIdent "quotRem")) :>: (Forall [Star]
                   ([isIn1 cIntegral (TGen 0)] :=> 
                    (TGen 0 `fn` TGen 0 `fn` TTuple [TGen 0, TGen 0])))
divModMfun
 = (AQual (AModule "Prelude") (AHsIdent "divMod")) :>: (Forall [Star]
                  ([isIn1 cIntegral (TGen 0)] :=> 
                   (TGen 0 `fn` TGen 0 `fn` TTuple [TGen 0, TGen 0])))
evenMfun
 = (AQual (AModule "Prelude") (AHsIdent "even")) :>: (Forall [Star]
                ([isIn1 cIntegral (TGen 0)] :=> 
                 (TGen 0 `fn` tBool)))
oddMfun
 = (AQual (AModule "Prelude") (AHsIdent "odd")) :>: (Forall [Star]
               ([isIn1 cIntegral (TGen 0)] :=> 
                (TGen 0 `fn` tBool)))
toIntegerMfun
 = (AQual (AModule "Prelude") (AHsIdent "toInteger")) :>: (Forall [Star]
                     ([isIn1 cIntegral (TGen 0)] :=> 
                      (TGen 0 `fn` tInteger)))
toIntMfun
 = (AQual (AModule "Prelude") (AHsIdent "toInt")) :>: (Forall [Star]
                 ([isIn1 cIntegral (TGen 0)] :=> 
                  (TGen 0 `fn` tInt)))

instsIntegral
 = [mkInst []
     ([] :=> 
      isIn1 cIntegral tInt),
    mkInst []
     ([] :=> 
      isIn1 cIntegral tInteger)]

-- methodSigsIntegral :: [(AHsDecl)]
methodSigsIntegral 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "quot",AUnQual "rem",AUnQual "div",AUnQual "mod"] 
               (AHsAQualType [(AUnQual "Integral", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc
           [AUnQual "quotRem",AUnQual "divMod"] 
              (AHsAQualType [(AUnQual "Integral", AUnQual "a")]
                 (AHsTyFun (AHsTyVar (AUnQual "a")) 
                     (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyTuple [AHsTyVar (AUnQual "a"),AHsTyVar (AUnQual "a")])))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "even",AUnQual "odd"] 
               (AHsAQualType [(AUnQual "Integral", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool")))),

      AHsTypeSig 
         bogusSrcLoc
            [AUnQual "toInteger"] 
               (AHsAQualType [(AUnQual "Integral", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Integer")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "toInt"] 
               (AHsAQualType [(AUnQual "Integral", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Int"))))

      -}
     ]

cFractional = AQual (AModule "Prelude") (AHsIdent "Fractional")
cFractionalTriple = ((AQual (AModule "Prelude") (AHsIdent "Fractional")), ([cNum], instsFractional, methodSigsFractional))

divideMfun
 = (AQual (AModule "Prelude") (AHsIdent "/")) :>: (Forall [Star]
             ([isIn1 cFractional (TGen 0)] :=> 
              (TGen 0 `fn` TGen 0 `fn` TGen 0)))
recipMfun
 = (AQual (AModule "Prelude") (AHsIdent "recip")) :>: (Forall [Star]
                 ([isIn1 cFractional (TGen 0)] :=> 
                  (TGen 0 `fn` TGen 0)))
fromRationalMfun
 = (AQual (AModule "Prelude") (AHsIdent "fromRational")) :>: (Forall [Star]
                        ([isIn1 cFractional (TGen 0)] :=> 
                         (tRational `fn` TGen 0)))
fromDoubleMfun
 = (AQual (AModule "Prelude") (AHsIdent "fromDouble")) :>: (Forall [Star]
                      ([isIn1 cFractional (TGen 0)] :=> 
                       (tDouble `fn` TGen 0)))

instsFractional
 = [mkInst []
     ([] :=> 
      isIn1 cFractional tFloat),
    mkInst []
     ([] :=> 
      isIn1 cFractional tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cFractional (TAp tRatio (TGen 0)))]

-- methodSigsFractional :: [(AHsDecl)]
methodSigsFractional 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "/"] 
               (AHsAQualType [(AUnQual "Fractional", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
        bogusSrcLoc
           [AUnQual "recip"] 
              (AHsAQualType [(AUnQual "Fractional", AUnQual "a")]
                 (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc
            [AUnQual "fromRational"] 
               (AHsAQualType [(AUnQual "Fractional", AUnQual "a")]
                  (AHsTyFun (AHsTyCon (AUnQual "Rational")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc
            [AUnQual "fromDouble"] 
               (AHsAQualType [(AUnQual "Fractional", AUnQual "a")] 
                  (AHsTyFun (AHsTyCon (AUnQual "Double")) (AHsTyVar (AUnQual "a"))))
       -}
     ]

cFloating = AQual (AModule "Prelude") (AHsIdent "Floating")
cFloatingTriple = ((AQual (AModule "Prelude") (AHsIdent "Floating")), ([cFractional], instsFloating, methodSigsFloating))

piMfun
 = (AQual (AModule "Prelude") (AHsIdent "pi")) :>: (Forall [Star]
              ([isIn1 cFloating (TGen 0)] :=> 
               (TGen 0)))
expMfun
 = (AQual (AModule "Prelude") (AHsIdent "exp")) :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0)))
logMfun
 = (AQual (AModule "Prelude") (AHsIdent "log")) :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0)))
sqrtMfun
 = (AQual (AModule "Prelude") (AHsIdent "sqrt")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
starstarMfun
 = (AQual (AModule "Prelude") (AHsIdent "**")) :>: (Forall [Star]
              ([isIn1 cFloating (TGen 0)] :=> 
               (TGen 0 `fn` TGen 0 `fn` TGen 0)))
logBaseMfun
 = (AQual (AModule "Prelude") (AHsIdent "logBase")) :>: (Forall [Star]
                   ([isIn1 cFloating (TGen 0)] :=> 
                    (TGen 0 `fn` TGen 0 `fn` TGen 0)))
sinMfun
 = (AQual (AModule "Prelude") (AHsIdent "sin")) :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0)))
cosMfun
 = (AQual (AModule "Prelude") (AHsIdent "cos")) :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0)))
tanMfun
 = (AQual (AModule "Prelude") (AHsIdent "tan")) :>: (Forall [Star]
               ([isIn1 cFloating (TGen 0)] :=> 
                (TGen 0 `fn` TGen 0)))
asinMfun
 = (AQual (AModule "Prelude") (AHsIdent "asin")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
acosMfun
 = (AQual (AModule "Prelude") (AHsIdent "acos")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
atanMfun
 = (AQual (AModule "Prelude") (AHsIdent "atan")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
sinhMfun
 = (AQual (AModule "Prelude") (AHsIdent "sinh")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
coshMfun
 = (AQual (AModule "Prelude") (AHsIdent "cosh")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
tanhMfun
 = (AQual (AModule "Prelude") (AHsIdent "tanh")) :>: (Forall [Star]
                ([isIn1 cFloating (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
asinhMfun
 = (AQual (AModule "Prelude") (AHsIdent "asinh")) :>: (Forall [Star]
                 ([isIn1 cFloating (TGen 0)] :=> 
                  (TGen 0 `fn` TGen 0)))
acoshMfun
 = (AQual (AModule "Prelude") (AHsIdent "acosh")) :>: (Forall [Star]
                 ([isIn1 cFloating (TGen 0)] :=> 
                  (TGen 0 `fn` TGen 0)))
atanhMfun
 = (AQual (AModule "Prelude") (AHsIdent "atanh")) :>: (Forall [Star]
                 ([isIn1 cFloating (TGen 0)] :=> 
                  (TGen 0 `fn` TGen 0)))

instsFloating
 = [mkInst []
     ([] :=> 
      isIn1 cFloating tFloat),
    mkInst []
     ([] :=> 
      isIn1 cFloating tDouble)]

-- methodSigsFloating :: [(AHsDecl)]
methodSigsFloating 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "pi"] 
               (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                  (AHsTyVar (AUnQual "a"))),

      AHsTypeSig 
         bogusSrcLoc
            [AUnQual "exp",AUnQual "log",AUnQual "sqrt"] 
               (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "**",AUnQual "logBase"] 
               (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "sin",AUnQual "cos",AUnQual "tan"] 
               (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                   (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc
           [AUnQual "asin",AUnQual "acos",AUnQual "atan"] 
              (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                 (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc
            [AUnQual "sinh",AUnQual "cosh",AUnQual "tanh"] 
               (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc
            [AUnQual "asinh",AUnQual "acosh",AUnQual "atanh"] 
               (AHsAQualType [(AUnQual "Floating", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))
         -}
     ]


cRealFrac = AQual (AModule "Prelude") (AHsIdent "RealFrac")
cRealFracTriple = ((AQual (AModule "Prelude") (AHsIdent "RealFrac")), ([cReal, cFractional], instsRealFrac, methodSigsRealFrac))

properFractionMfun
 = (AQual (AModule "Prelude") (AHsIdent "properFraction")) :>: (Forall [Star, Star]
                          ([isIn1 cRealFrac (TGen 0),
                            isIn1 cIntegral (TGen 1)] :=> 
                           (TGen 0 `fn` TTuple [TGen 1, TGen 0])))
truncateMfun
 = (AQual (AModule "Prelude") (AHsIdent "truncate")) :>: (Forall [Star, Star]
                    ([isIn1 cRealFrac (TGen 0),
                      isIn1 cIntegral (TGen 1)] :=> 
                     (TGen 0 `fn` TGen 1)))
roundMfun
 = (AQual (AModule "Prelude") (AHsIdent "round")) :>: (Forall [Star, Star]
                 ([isIn1 cRealFrac (TGen 0),
                   isIn1 cIntegral (TGen 1)] :=> 
                  (TGen 0 `fn` TGen 1)))
ceilingMfun
 = (AQual (AModule "Prelude") (AHsIdent "ceiling")) :>: (Forall [Star, Star]
                   ([isIn1 cRealFrac (TGen 0),
                     isIn1 cIntegral (TGen 1)] :=> 
                    (TGen 0 `fn` TGen 1)))
floorMfun
 = (AQual (AModule "Prelude") (AHsIdent "floor")) :>: (Forall [Star, Star]
                 ([isIn1 cRealFrac (TGen 0),
                   isIn1 cIntegral (TGen 1)] :=> 
                  (TGen 0 `fn` TGen 1)))

instsRealFrac
 = [mkInst []
     ([] :=> 
      isIn1 cRealFrac tFloat),
    mkInst []
     ([] :=> 
      isIn1 cRealFrac tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cRealFrac (TAp tRatio (TGen 0)))]

-- methodSigsRealFrac :: [(AHsDecl)]
methodSigsRealFrac 
   = [

      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "properFraction"] 
               (AHsAQualType [(AUnQual "RealFrac", AUnQual "a"), (AUnQual "Integral",AUnQual "b")] 
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyTuple [AHsTyVar (AUnQual "b"),AHsTyVar (AUnQual "a")]))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "truncate",AUnQual "round"] 
               (AHsAQualType [(AUnQual "RealFrac", AUnQual "a"), (AUnQual "Integral",AUnQual "b")] 
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "b")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "ceiling",AUnQual "floor"] 
               (AHsAQualType [(AUnQual "RealFrac", AUnQual "a"),(AUnQual "Integral",AUnQual "b")] 
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "b"))))
       -}
     ]

cRealFloat = AQual (AModule "Prelude") (AHsIdent "RealFloat")
cRealFloatTriple = ((AQual (AModule "Prelude") (AHsIdent "RealFloat")), ([cRealFrac, cFloating], instsRealFloat, methodSigsRealFloat))

floatRadixMfun
 = (AQual (AModule "Prelude") (AHsIdent "floatRadix")) :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (TGen 0 `fn` tInteger)))
floatDigitsMfun
 = (AQual (AModule "Prelude") (AHsIdent "floatDigits")) :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (TGen 0 `fn` tInt)))
floatRangeMfun
 = (AQual (AModule "Prelude") (AHsIdent "floatRange")) :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (TGen 0 `fn` TTuple [tInt, tInt])))
decodeFloatMfun
 = (AQual (AModule "Prelude") (AHsIdent "decodeFloat")) :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (TGen 0 `fn` TTuple [tInteger, tInt])))
encodeFloatMfun
 = (AQual (AModule "Prelude") (AHsIdent "encodeFloat")) :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (tInteger `fn` tInt `fn` TGen 0)))
exponentMfun
 = (AQual (AModule "Prelude") (AHsIdent "exponent")) :>: (Forall [Star]
                    ([isIn1 cRealFloat (TGen 0)] :=> 
                     (TGen 0 `fn` tInt)))
significandMfun
 = (AQual (AModule "Prelude") (AHsIdent "significand")) :>: (Forall [Star]
                       ([isIn1 cRealFloat (TGen 0)] :=> 
                        (TGen 0 `fn` TGen 0)))
scaleFloatMfun
 = (AQual (AModule "Prelude") (AHsIdent "scaleFloat")) :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (tInt `fn` TGen 0 `fn` TGen 0)))
isNaNMfun
 = (AQual (AModule "Prelude") (AHsIdent "isNaN")) :>: (Forall [Star]
                 ([isIn1 cRealFloat (TGen 0)] :=> 
                  (TGen 0 `fn` tBool)))
isInfiniteMfun
 = (AQual (AModule "Prelude") (AHsIdent "isInfinite")) :>: (Forall [Star]
                      ([isIn1 cRealFloat (TGen 0)] :=> 
                       (TGen 0 `fn` tBool)))
isDenormalizedMfun
 = (AQual (AModule "Prelude") (AHsIdent "isDenormalized")) :>: (Forall [Star]
                          ([isIn1 cRealFloat (TGen 0)] :=> 
                           (TGen 0 `fn` tBool)))
isNegativeZeroMfun
 = (AQual (AModule "Prelude") (AHsIdent "isNegativeZero")) :>: (Forall [Star]
                          ([isIn1 cRealFloat (TGen 0)] :=> 
                           (TGen 0 `fn` tBool)))
isIEEEMfun
 = (AQual (AModule "Prelude") (AHsIdent "isIEEE")) :>: (Forall [Star]
                  ([isIn1 cRealFloat (TGen 0)] :=> 
                   (TGen 0 `fn` tBool)))
atan2Mfun
 = (AQual (AModule "Prelude") (AHsIdent "atan2")) :>: (Forall [Star]
                 ([isIn1 cRealFloat (TGen 0)] :=> 
                  (TGen 0 `fn` TGen 0 `fn` TGen 0)))

instsRealFloat
 = [mkInst []
     ([] :=> 
      isIn1 cRealFloat tFloat),
    mkInst []
     ([] :=> 
      isIn1 cRealFloat tDouble)]

-- methodSigsRealFloat :: [(AHsDecl)]

methodSigsRealFloat 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual (AHsIdent "floatRadix")] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Integer")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "floatDigits"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Int")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "floatRange"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyTuple [AHsTyCon (AUnQual "Int"),AHsTyCon (AUnQual "Int")]))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "decodeFloat"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyTuple [AHsTyCon (AUnQual "Integer"),AHsTyCon (AUnQual "Int")]))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "encodeFloat"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyCon (AUnQual "Integer")) (AHsTyFun (AHsTyCon (AUnQual "Int")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "exponent"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Int")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "significand"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "scaleFloat"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyCon (AUnQual "Int")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "isNaN",AUnQual "isInfinite",AUnQual "isDenormalized",AUnQual "isNegativeZero",AUnQual "isIEEE"] 
               (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool")))),

      AHsTypeSig 
         bogusSrcLoc [AUnQual "atan2"] 
            (AHsAQualType [(AUnQual "RealFloat", AUnQual "a")]
               (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))))
      -}
     ]

cIx = AQual (AModule "Prelude") (AHsIdent "Ix")
cIxTriple = ((AQual (AModule "Prelude") (AHsIdent "Ix")), ([cOrd], instsIx, methodSigsIx))

rangeMfun
 = (AQual (AModule "Prelude") (AHsIdent "range")) :>: (Forall [Star]
                 ([isIn1 cIx (TGen 0)] :=> 
                  (TTuple [TGen 0, TGen 0] `fn` TAp tList (TGen 0))))
indexMfun
 = (AQual (AModule "Prelude") (AHsIdent "index")) :>: (Forall [Star]
                 ([isIn1 cIx (TGen 0)] :=> 
                  (TTuple [TGen 0, TGen 0] `fn` TGen 0 `fn` tInt)))
inRangeMfun
 = (AQual (AModule "Prelude") (AHsIdent "inRange")) :>: (Forall [Star]
                   ([isIn1 cIx (TGen 0)] :=> 
                    (TTuple [TGen 0, TGen 0] `fn` TGen 0 `fn` tBool)))
rangeSizeMfun
 = (AQual (AModule "Prelude") (AHsIdent "rangeSize")) :>: (Forall [Star]
                     ([isIn1 cIx (TGen 0)] :=> 
                      (TTuple [TGen 0, TGen 0] `fn` tInt)))

instsIx
 = [mkInst []
     ([] :=> 
      isIn1 cIx tUnit),
    mkInst []
     ([] :=> 
      isIn1 cIx tChar),
    mkInst []
     ([] :=> 
      isIn1 cIx tInt),
    mkInst []
     ([] :=> 
      isIn1 cIx tInteger),
    mkInst []
     ([] :=> 
      isIn1 cIx tBool),
    mkInst []
     ([] :=> 
      isIn1 cIx tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1),
       isIn1 cIx (TGen 2),
       isIn1 cIx (TGen 3),
       isIn1 cIx (TGen 4)] :=> 
      isIn1 cIx (TTuple [TGen 0, TGen 1, TGen 2, TGen 3, TGen 4])),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1),
       isIn1 cIx (TGen 2),
       isIn1 cIx (TGen 3)] :=> 
      isIn1 cIx (TTuple [TGen 0, TGen 1, TGen 2, TGen 3])),
    mkInst [Star, Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1),
       isIn1 cIx (TGen 2)] :=> 
      isIn1 cIx (TTuple [TGen 0, TGen 1, TGen 2])),
    mkInst [Star, Star]
     ([isIn1 cIx (TGen 0),
       isIn1 cIx (TGen 1)] :=> 
      isIn1 cIx (TTuple [TGen 0, TGen 1]))]

-- methodSigsIx :: [(AHsDecl)]
methodSigsIx 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "range"] 
               (AHsAQualType [(AUnQual "Ix", AUnQual "a")]
                  (AHsTyFun (AHsTyTuple [AHsTyVar (AUnQual "a"),AHsTyVar (AUnQual "a")]) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "index"] 
               (AHsAQualType [(AUnQual "Ix", AUnQual "a")]
                  (AHsTyFun (AHsTyTuple [AHsTyVar (AUnQual "a"),AHsTyVar (AUnQual "a")]) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Int"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "inRange"] 
               (AHsAQualType [(AUnQual "Ix", AUnQual "a")]
                  (AHsTyFun (AHsTyTuple [AHsTyVar (AUnQual "a"),AHsTyVar (AUnQual "a")]) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Bool"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "rangeSize"] 
               (AHsAQualType [(AUnQual "Ix", AUnQual "a")]
                  (AHsTyFun (AHsTyTuple [AHsTyVar (AUnQual "a"),AHsTyVar (AUnQual "a")]) (AHsTyCon (AUnQual "Int"))))
       -}
     ]

cEnum = AQual (AModule "Prelude") (AHsIdent "Enum")
cEnumTriple = ((AQual (AModule "Prelude") (AHsIdent "Enum")), ([], instsEnum, methodSigsEnum))

succMfun
 = (AQual (AModule "Prelude") (AHsIdent "succ")) :>: (Forall [Star]
                ([isIn1 cEnum (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
predMfun
 = (AQual (AModule "Prelude") (AHsIdent "pred")) :>: (Forall [Star]
                ([isIn1 cEnum (TGen 0)] :=> 
                 (TGen 0 `fn` TGen 0)))
toEnumMfun
 = (AQual (AModule "Prelude") (AHsIdent "toEnum")) :>: (Forall [Star]
                  ([isIn1 cEnum (TGen 0)] :=> 
                   (tInt `fn` TGen 0)))
fromEnumMfun
 = (AQual (AModule "Prelude") (AHsIdent "fromEnum")) :>: (Forall [Star]
                    ([isIn1 cEnum (TGen 0)] :=> 
                     (TGen 0 `fn` tInt)))
enumFromMfun
 = (AQual (AModule "Prelude") (AHsIdent "enumFrom")) :>: (Forall [Star]
                    ([isIn1 cEnum (TGen 0)] :=> 
                     (TGen 0 `fn` TAp tList (TGen 0))))
enumFromThenMfun
 = (AQual (AModule "Prelude") (AHsIdent "enumFromThen")) :>: (Forall [Star]
                        ([isIn1 cEnum (TGen 0)] :=> 
                         (TGen 0 `fn` TGen 0 `fn` TAp tList (TGen 0))))
enumFromToMfun
 = (AQual (AModule "Prelude") (AHsIdent "enumFromTo")) :>: (Forall [Star]
                      ([isIn1 cEnum (TGen 0)] :=> 
                       (TGen 0 `fn` TGen 0 `fn` TAp tList (TGen 0))))
enumFromThenToMfun
 = (AQual (AModule "Prelude") (AHsIdent "enumFromThenTo")) :>: (Forall [Star]
                          ([isIn1 cEnum (TGen 0)] :=> 
                           (TGen 0 `fn` TGen 0 `fn` TGen 0 `fn` TAp tList (TGen 0))))

instsEnum
 = [mkInst []
     ([] :=> 
      isIn1 cEnum tUnit),
    mkInst []
     ([] :=> 
      isIn1 cEnum tChar),
    mkInst []
     ([] :=> 
      isIn1 cEnum tInt),
    mkInst []
     ([] :=> 
      isIn1 cEnum tInteger),
    mkInst []
     ([] :=> 
      isIn1 cEnum tFloat),
    mkInst []
     ([] :=> 
      isIn1 cEnum tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cEnum (TAp tRatio (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cEnum tBool),
    mkInst []
     ([] :=> 
      isIn1 cEnum tOrdering)]

-- methodSigsEnum :: [(AHsDecl)]
methodSigsEnum 
   = [
      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "succ",AUnQual "pred"] 
               (AHsAQualType [(AUnQual "Enum", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "toEnum"] 
               (AHsAQualType [(AUnQual "Enum", AUnQual "a")]
                  (AHsTyFun (AHsTyCon (AUnQual "Int")) (AHsTyVar (AUnQual "a")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "fromEnum"] 
               (AHsAQualType [(AUnQual "Enum", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyCon (AUnQual "Int")))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "enumFrom"] 
               (AHsAQualType [(AUnQual "Enum", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "enumFromThen"] 
                (AHsAQualType [(AUnQual "Enum", AUnQual "a")] 
                   (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a")))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "enumFromTo"] 
               (AHsAQualType [(AUnQual "Enum", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a")))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "enumFromThenTo"] 
               (AHsAQualType [(AUnQual "Enum", AUnQual "a")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a")))))))
       
       -}

     ]

cRead = AQual (AModule "Prelude") (AHsIdent "Read")
cReadTriple = ((AQual (AModule "Prelude") (AHsIdent "Read")), ([], instsRead, methodSigsRead))

readsPrecMfun
 = (AQual (AModule "Prelude") (AHsIdent "readsPrec")) :>: (Forall [Star]
                     ([isIn1 cRead (TGen 0)] :=> 
                      (tInt `fn` tReadS (TGen 0))))
readListMfun
 = (AQual (AModule "Prelude") (AHsIdent "readList")) :>: (Forall [Star]
                    ([isIn1 cRead (TGen 0)] :=> 
                     tReadS (TAp tList (TGen 0))))

instsRead
 = [mkInst []
     ([] :=> 
      isIn1 cRead tUnit),
    mkInst []
     ([] :=> 
      isIn1 cRead tChar),
    mkInst [Star]
     ([isIn1 cRead (TGen 0)] :=> 
      isIn1 cRead (TAp tList (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cRead tInt),
    mkInst []
     ([] :=> 
      isIn1 cRead tInteger),
    mkInst []
     ([] :=> 
      isIn1 cRead tFloat),
    mkInst []
     ([] :=> 
      isIn1 cRead tDouble),
    mkInst [Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cRead (TAp tRatio (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cRead tBool),
    mkInst [Star]
     ([isIn1 cRead (TGen 0)] :=> 
      isIn1 cRead (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1)] :=> 
      isIn1 cRead (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst []
     ([] :=> 
      isIn1 cRead tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1),
       isIn1 cRead (TGen 2),
       isIn1 cRead (TGen 3),
       isIn1 cRead (TGen 4)] :=> 
      isIn1 cRead (TTuple [TGen 0, TGen 1, TGen 2, TGen 3, TGen 4])),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1),
       isIn1 cRead (TGen 2),
       isIn1 cRead (TGen 3)] :=> 
      isIn1 cRead (TTuple [TGen 0, TGen 1, TGen 2, TGen 3])),
    mkInst [Star, Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1),
       isIn1 cRead (TGen 2)] :=> 
      isIn1 cRead (TTuple [TGen 0, TGen 1, TGen 2])),
    mkInst [Star, Star]
     ([isIn1 cRead (TGen 0),
       isIn1 cRead (TGen 1)] :=> 
      isIn1 cRead (TTuple [TGen 0, TGen 1]))]

-- methodSigsRead :: [(AHsDecl)]
methodSigsRead 
   = [
       {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual (AQual (AModule "Prelude") "readsPrec")] 
               (AHsAQualType [(AUnQual "Read", AUnQual "a")]
                  (AHsTyFun (AHsTyCon (AUnQual "Int")) (AHsTyFun (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyTuple [AHsTyVar (AUnQual "a"),AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))]))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "readList"] 
               (AHsAQualType [(AUnQual "Read", AUnQual "a")]
                  (AHsTyFun (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyTuple [AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a")),AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))]))))

       -}
     ]

cShow = AQual (AModule "Prelude") (AHsIdent "Show")
cShowTriple = ((AQual (AModule "Prelude") (AHsIdent "Show")), ([], instsShow, methodSigsShow))

showMfun
 = (AQual (AModule "Prelude") (AHsIdent "show")) :>: (Forall [Star]
                ([isIn1 cShow (TGen 0)] :=> 
                 (TGen 0 `fn` tString)))
showsPrecMfun
 = (AQual (AModule "Prelude") (AHsIdent "showsPrec")) :>: (Forall [Star]
                     ([isIn1 cShow (TGen 0)] :=> 
                      (tInt `fn` TGen 0 `fn` tShowS)))
showListMfun
 = (AQual (AModule "Prelude") (AHsIdent "showList")) :>: (Forall [Star]
                    ([isIn1 cShow (TGen 0)] :=> 
                     (TAp tList (TGen 0) `fn` tShowS)))

instsShow
 = [mkInst []
     ([] :=> 
      isIn1 cShow tUnit),
    mkInst []
     ([] :=> 
      isIn1 cShow tChar),
    mkInst [Star]
     ([isIn1 cShow (TGen 0)] :=> 
      isIn1 cShow (TAp tList (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cShow tInt),
    mkInst []
     ([] :=> 
      isIn1 cShow tInteger),
    mkInst []
     ([] :=> 
      isIn1 cShow tFloat),
    mkInst []
     ([] :=> 
      isIn1 cShow tDouble),
    mkInst [Star]
     ([isIn1 cIntegral (TGen 0)] :=> 
      isIn1 cShow (TAp tRatio (TGen 0))),
    mkInst [Star]
     ([] :=> 
      isIn1 cShow (TAp tIO (TGen 0))),
    mkInst []
     ([] :=> 
      isIn1 cShow tIOError),
    mkInst []
     ([] :=> 
      isIn1 cShow tBool),
    mkInst [Star]
     ([isIn1 cShow (TGen 0)] :=> 
      isIn1 cShow (TAp tMaybe (TGen 0))),
    mkInst [Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1)] :=> 
      isIn1 cShow (TAp (TAp tEither (TGen 0)) (TGen 1))),
    mkInst []
     ([] :=> 
      isIn1 cShow tOrdering),
    mkInst [Star, Star, Star, Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1),
       isIn1 cShow (TGen 2),
       isIn1 cShow (TGen 3),
       isIn1 cShow (TGen 4)] :=> 
      isIn1 cShow (TTuple [TGen 0, TGen 1, TGen 2, TGen 3, TGen 4])),
    mkInst [Star, Star, Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1),
       isIn1 cShow (TGen 2),
       isIn1 cShow (TGen 3)] :=> 
      isIn1 cShow (TTuple [TGen 0, TGen 1, TGen 2, TGen 3])),
    mkInst [Star, Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1),
       isIn1 cShow (TGen 2)] :=> 
      isIn1 cShow (TTuple [TGen 0, TGen 1, TGen 2])),
    mkInst [Star, Star]
     ([isIn1 cShow (TGen 0),
       isIn1 cShow (TGen 1)] :=> 
      isIn1 cShow (TTuple [TGen 0, TGen 1]))]

-- methodSigsShow :: [(AHsDecl)]
methodSigsShow 
   = [


      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "show"] 
               (AHsAQualType [(AUnQual "Show", AUnQual "a")]
                 (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "showsPrec"] 
               (AHsAQualType [(AUnQual "Show", AUnQual "a")]
                  (AHsTyFun (AHsTyCon (AUnQual "Int")) (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyFun (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "showList"] 
               (AHsAQualType [(AUnQual "Show", AUnQual "a")]
                  (AHsTyFun (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyVar (AUnQual "a"))) (AHsTyFun (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))) (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))))))

        -}
     ]

cFunctor = AQual (AModule "Prelude") (AHsIdent "Functor")
cFunctorTriple = ((AQual (AModule "Prelude") (AHsIdent "Functor")), ([], instsFunctor, methodSigsFunctor))

fmapMfun
 = (AQual (AModule "Prelude") (AHsIdent "fmap")) :>: (Forall [Kfun Star Star, Star, Star]
                ([isIn1 cFunctor (TGen 0)] :=> 
                 ((TGen 1 `fn` TGen 2) `fn` TAp (TGen 0) (TGen 1) `fn` TAp (TGen 0) (TGen 2))))

instsFunctor
 = [mkInst []
     ([] :=> 
      isIn1 cFunctor tMaybe),
    mkInst []
     ([] :=> 
      isIn1 cFunctor tList),
    mkInst []
     ([] :=> 
      isIn1 cFunctor tIO)]

-- methodSigsFunctor :: [(AHsDecl)]
methodSigsFunctor 
   = [

      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "fmap"] 
               (AHsAQualType [(AUnQual "Functor", AUnQual "f")]
                  (AHsTyFun (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyVar (AUnQual "b"))) (AHsTyFun (AHsTyApp (AHsTyVar (AUnQual "f")) (AHsTyVar (AUnQual "a"))) (AHsTyApp (AHsTyVar (AUnQual "f")) (AHsTyVar (AUnQual "b"))))))

      -}
     ]

cMonad = AQual (AModule "Prelude") (AHsIdent "Monad")
cMonadTriple = ((AQual (AModule "Prelude") (AHsIdent "Monad")), ([], instsMonad, methodSigsMonad))

returnMfun
 = (AQual (AModule "Prelude") (AHsIdent "return")) :>: (Forall [Kfun Star Star, Star]
                  ([isIn1 cMonad (TGen 0)] :=> 
                   (TGen 1 `fn` TAp (TGen 0) (TGen 1))))
mbindMfun
 = (AQual (AModule "Prelude") (AHsSymbol ">>=")) :>: (Forall [Kfun Star Star, Star, Star]
               ([isIn1 cMonad (TGen 0)] :=> 
                (TAp (TGen 0) (TGen 1) `fn` (TGen 1 `fn` TAp (TGen 0) (TGen 2)) `fn` TAp (TGen 0) (TGen 2))))
mthenMfun
 = (AQual (AModule "Prelude") (AHsSymbol ">>")) :>: (Forall [Kfun Star Star, Star, Star]
              ([isIn1 cMonad (TGen 0)] :=> 
               (TAp (TGen 0) (TGen 1) `fn` TAp (TGen 0) (TGen 2) `fn` TAp (TGen 0) (TGen 2))))
failMfun
 = (AQual (AModule "Prelude") (AHsIdent "fail")) :>: (Forall [Kfun Star Star, Star]
                ([isIn1 cMonad (TGen 0)] :=> 
                 (tString `fn` TAp (TGen 0) (TGen 1))))

instsMonad
 = [mkInst []
     ([] :=> 
      isIn1 cMonad tMaybe),
    mkInst []
     ([] :=> 
      isIn1 cMonad tList),
    mkInst []
     ([] :=> 
      isIn1 cMonad tIO) {-,
    mkInst []
     ([] :=> 
      isIn1 cMonad tTI)-}]

-- methodSigsMonad :: [(AHsDecl)]
methodSigsMonad 
   = [

      {-
      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "return"] 
               (AHsAQualType [(AUnQual "Monad", AUnQual "m")]
                  (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "a"))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual ">>="] 
                (AHsAQualType [(AUnQual "Monad", AUnQual "m")]
                    (AHsTyFun (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "a"))) (AHsTyFun (AHsTyFun (AHsTyVar (AUnQual "a")) (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "b")))) (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "b")))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual ">>"] 
               (AHsAQualType [(AUnQual "Monad", AUnQual "m")]
                  (AHsTyFun (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "a"))) (AHsTyFun (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "b"))) (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "b")))))),

      AHsTypeSig 
         bogusSrcLoc 
            [AUnQual "fail"] 
               (AHsAQualType [(AUnQual "Monad", AUnQual "m")]
                  (AHsTyFun (AHsTyApp (AHsTyCon (AUnQual "[]")) (AHsTyCon (AUnQual "Char"))) (AHsTyApp (AHsTyVar (AUnQual "m")) (AHsTyVar (AUnQual "a")))))

        -}
     ]

preludeClasses 
   = [cEqTriple,
      cOrdTriple,
      cBoundedTriple,
      cNumTriple,
      cRealTriple,
      cIntegralTriple,
      cFractionalTriple,
      cFloatingTriple,
      cRealFracTriple,
      cRealFloatTriple,
      cIxTriple, 
      cEnumTriple,
      cReadTriple,
      cShowTriple,
      cFunctorTriple,
      cMonadTriple
     ]    

preludeMethods
   = concat
        [methodSigsEq,
         methodSigsOrd,
         methodSigsBounded,
         methodSigsNum,
         methodSigsReal,
         methodSigsIntegral,
         methodSigsFractional,
         methodSigsFloating,
         methodSigsRealFrac,
         methodSigsRealFloat,
         methodSigsIx,
         methodSigsEnum,
         methodSigsRead,
         methodSigsShow,
         methodSigsFunctor,
         methodSigsMonad
        ]

-- Synonyms from the Prelude

preludeSynonyms
   = [AHsTypeDecl bogusASrcLoc 
                 (AQual (AModule "Prelude") (AHsIdent "String")) 
                 [] 
                 (AHsTyApp 
                    (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "[]"))) 
                    (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "Char")))),

      AHsTypeDecl bogusASrcLoc
                 (AQual (AModule "Prelude") (AHsIdent "Rational"))
                 []
                 (AHsTyApp
                    (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "Ratio")))
                    (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "Integer")))),

      AHsTypeDecl bogusASrcLoc  
                 (AQual (AModule "Prelude") (AHsIdent "ReadS"))
                 [AUnQual (AHsIdent "a")] 
                    (AHsTyFun 
                       (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "String"))) 
                       (AHsTyApp (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "[]"))) (AHsTyTuple [AHsTyVar (AUnQual (AHsIdent "a")),AHsTyCon (AQual (AModule "Prelude") (AHsIdent "String"))]))),

      AHsTypeDecl bogusASrcLoc 
                 (AQual (AModule "Prelude") (AHsIdent "ShowS")) 
                 [] 
                 (AHsTyFun (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "String"))) (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "String")))),

      AHsTypeDecl bogusASrcLoc
                 (AQual (AModule "Prelude") (AHsIdent "FilePath"))
                 []
                 (AHsTyCon (AQual (AModule "Prelude") (AHsIdent "String")))

     ]


{-
                        describes the kinds of type constructors introduced 
                        in the prelude. Again, just for bootstrapping
                        purposes, one day this should disappear
-}

preludeTyconAndClassKinds :: [(AHsName, Kind)]
preludeTyconAndClassKinds
   = [ -- type contructors
       (AQual (AModule "Prelude") (AHsIdent "[]"), Star `Kfun` Star),
       (AQual (AModule "Prelude") (AHsIdent "Maybe"), Star `Kfun` Star),
       (AQual (AModule "Prelude") (AHsIdent "Bool"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Char"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Either"), Star `Kfun` (Star `Kfun` Star)),
       (AQual (AModule "Prelude") (AHsIdent "Ordering"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Int"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Integer"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Float"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Double"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Ratio"), Star),
       (AQual (AModule "Prelude") (AHsIdent "IOError"), Star),
       (AQual (AModule "Prelude") (AHsIdent "IO"), Star `Kfun` Star),
       (AQual (AModule "Prelude") (AHsSpecial "()"), Star),
       -- classes
       (AQual (AModule "Prelude") (AHsIdent "Eq"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Ord"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Bounded"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Num"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Real"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Integral"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Fractional"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Floating"), Star),
       (AQual (AModule "Prelude") (AHsIdent "RealFrac"), Star),
       (AQual (AModule "Prelude") (AHsIdent "RealFloat"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Ix"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Enum"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Read"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Show"), Star),
       (AQual (AModule "Prelude") (AHsIdent "Functor"), Star `Kfun` Star),
       (AQual (AModule "Prelude") (AHsIdent "Monad"), Star `Kfun` Star)
     ]
