module Type where

import Id

-- simple Id
simpleId :: String -> Id
simpleId(s) = Id [Token(s, nullPos)] [] 

-- same predefined type constructors
totalFunArrow = simpleId("->")
partialFunArrow = simpleId("->?")
productSign = simpleId("*")

internalBoolRep = simpleId("") -- invisible

-- ----------------------------------------------
-- we want to have (at least some builtin) type constructors 
-- for uniformity/generalization sorts get type "Sort"
-- "Sort -> Sort" would be the type/kind of a type constructor
-- ----------------------------------------------
data Type = Type Id [Type]
          | Sort
	    deriving (Eq, Ord)

showType :: Bool -> Type -> ShowS
showType _ Sort = showString "!SORT!"
showType _ t@(Type i []) = if isProduct t then showString "()" else shows i
showType b t@(Type i (x:r)) = showParen b 
 (if isFunType t 
  then showType (isFunType x) x . shows i . showType False (head r)
  else if isProduct t 
       then let showl [] = showString ""
                showl (y:t) = shows i . showType 
                              (isFunType y || isProduct y) y . showl t
            in showType (isFunType x || isProduct x) x . showl r
       else shows i . showList (x:r)
 )

instance Show Type where
    showsPrec p = showType (p > 0)

asType s = Type s []
-- ----------------------------------------------
-- builtin type
internalBool = asType internalBoolRep

-- function types, product type and the internal bool for predicates
totalFun  :: (Type, Type) -> Type 
totalFun(t1,t2) = Type totalFunArrow [t1,t2]
partialFun(t1,t2) = Type partialFunArrow [t1,t2]

predicate t = totalFun(t, internalBool)

isFunType(Type s  [_, _]) = (s == totalFunArrow) || (s == partialFunArrow)
isFunType _  = False

argType(Type _ [t, _]) = t
resType(Type _ [_, t]) = t

isPredicate t = isFunType t && (resType(t) == internalBool)

product = Type productSign
isProduct(Type s  _) = (s == productSign)
isPoduct _ = False

-- test if a type is first-order
isBaseType(Type _  l) = case l of {[] -> True ; _ -> False}
isBaseType Sort       = False -- not the type of a proper function 

-- first order types are products with 0, 1 or more arguments  
isFOArgType(t) = isProduct(t) && 
                  case t of { Type _ l -> all isBaseType l }  

-- constants are functions with the empty product as argument
isFOType(t) = isFunType(t) && isBaseType(resType(t)) && 
                           isFOArgType(argType(t))

