
{- HetCATS/HasCASL/Le.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   abstract syntax after/during static analysis
-}

module Le where

import Id
import Keywords
import HToken
import As(ExtClass(..), Class(..), Variance(..), ClassName)

type TypeId = Id

-- "*", "->", etc. are predefined type constructors
-- the unit type is the empty product

-----------------------------------------------------------------------------
-- Kinds
-----------------------------------------------------------------------------

data Kind  = Star ExtClass | Kfun Kind Kind deriving Show

isStar :: Kind -> Bool
isStar (Star _) = True
isStar (Kfun _ _) = False

showKind :: Kind -> ShowS
showKind (Star _) = showString prodS
showKind (Kfun k1 k2) = showParen (isStar k1) (showKind k1) 
			. showString funS . showKind k2

instance Eq Kind where
    Star _ == Star _ = True
    Kfun f1 a1 == Kfun f2 a2 = f1 == f2 && a1 == a2
    _ == _ = False

instance Ord Kind where
    Star _ <= Star _ = True
    Kfun f1 a1 <= Kfun f2 a2 = if f1 <= f2 then 
			       if f2 <= f1 then a1 <= a2
				  else True
			       else False
    Star _ <= Kfun _ _ = True
    Kfun _ _ <= Star _ = False

star :: Kind
star = Star $ ExtClass (Intersection [] []) InVar nullPos

-----------------------------------------------------------------------------
-- Types
-----------------------------------------------------------------------------

data Tyvar = Tyvar { typeVarId :: TypeId, typeKind :: Kind } 
	     deriving (Show, Eq, Ord)

data Tycon = Tycon TypeId Kind
             deriving (Show, Eq)

data Type  = TVar Tyvar | TCon Tycon | TAp Type Type | TGen Int
             deriving (Show, Eq)

tArrow :: Type
tArrow   = TCon (Tycon (Id [Token place nullPos, 
			    Token pFun nullPos,
			    Token place nullPos][][]) 
		 (Kfun star (Kfun star star)))

infixr      4 `fn`
fn         :: Type -> Type -> Type
a `fn` b    = TAp (TAp tArrow a) b

isInfixTycon, isInfixType :: Type -> Bool
isInfixTycon(TCon (Tycon i _)) = isInfix2 i
isInfixTycon _ = False

isInfixType(TAp (TAp t1 _) _) = isInfixTycon t1
isInfixType _ = False

showType :: Type -> ShowS
showType(TVar (Tyvar i k)) = showId i . noShow (isStar k)
			     (showString colonS . showKind k)
showType(TCon (Tycon i@(Id ts is _) _)) = 
    if isInfix2 i then showString  (tokStr $ head $ tail ts) . showIds is
    else showId i
showType(TAp t@(TAp t1 t2) t3) = 
    if isInfixTycon t1 then
       showParen (isInfixType t2) (showType t2) 
		     . showType t1 . showType t3
    else showType t . showChar ' ' . showType t3
showType(TAp t1 t2) = showType t1 . showChar ' ' . showType t2
showType(TGen i) = showParen True (showString "Gen " . shows i)

data Pred   = IsIn Id Type
              deriving (Show, Eq)

showPred :: Pred -> ShowS
showPred(IsIn i t) = showId i . showChar ' ' . showType t

data Qual t = [Pred] :=> t
              deriving (Show, Eq)

showQual :: (t -> ShowS) -> Qual t -> ShowS
showQual s (ps :=> t) = showParen (length ps > 1) 
			(showSepList (showString ",") showPred ps)
			. noShow (null ps) (showString implS) . s t

data Scheme = Scheme [Kind] (Qual Type)
              deriving (Show, Eq)

showScheme :: Scheme -> ShowS
showScheme(Scheme ks t) = 
    noShow (null ks) (showString forallS 
		      . showSepList (showChar ' ') showKind ks
		      . showString dotS) 
	       . showQual (showType) t
			  
-----------------------------------------------------------------------------
-- Symbols
-----------------------------------------------------------------------------

data SymbType = OpType Scheme
	      | TypeKind Kind
	      | Class

data Symbol = Symbol {symbId :: Id, sumbType :: SymbType}
-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

-----------------------------------------------------------------------------
-- Items
-----------------------------------------------------------------------------

data GenKind = Free | Generated | Loose deriving (Show, Eq)      

data VarDecl = VarDecl { varId :: Id, varType :: Type }

data TypeBody = Alias Type -- non-recursive
	      | Datatype [Alternative] GenKind GenItems
	      | SubtypeDefn VarDecl Type Term -- a formula

-- type variables correspond to the kind
data TypeDefn = TypeDefn [Tyvar] TypeBody

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id Type [Component] 
		 | Subtype Type

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) Type 

data ClassItem = ClassItem { classId :: ClassName
			   , superClasses :: [ClassName]
			   , classDefn :: Class
			   , instances :: [Qual Pred]
                           , classBody :: [SigItem]
			   }

newClassItem :: ClassName -> ClassItem
newClassItem cid = ClassItem cid [] (Intersection [] []) [] []

showClassItem :: ClassItem -> ShowS
showClassItem info =
    let Intersection syns _ = classDefn info
	sups = superClasses info
        insts = instances info
    in noShow (null syns) (showString equalS . showClassList syns)
    . noShow (null sups) (showString lessS . showClassList sups)
    . noShow (null insts) (showString "\ninstances: " .
			showSepList (showString ",") (showQual showPred) insts)

showClassList :: [ClassName] -> ShowS
showClassList is = showParen (length is > 1)
		   $ showSepList ("," ++) ((++) . tokStr) is


data TypeRel = TypeRel [Tyvar] Type Type

data TypeItem = TypeItem{ typeConstrId :: Id
			, itemKind :: Kind
			, subtypes :: [TypeRel]
			, supertypes :: [TypeRel]
			, typeDefn :: Maybe TypeDefn
			}

type ConsId = Symbol
type SelId = Symbol

data OpDefn = OpDef [VarDecl] Term
            | Constr ConsId
            | Select [ConsId] SelId

data BinOpAttr = Assoc | Comm | Idem deriving (Show) 

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term

data OpItem = OpItem { opId :: Id
		     , opType :: Scheme
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
		     }		      

data TypeOp = OfType | AsType | InType deriving (Eq)     

data Binder = LambdaTotal | LambdaPartial
	    | Forall 
            | Exists | ExistsUnique 
	    deriving (Eq)

data Term = BaseName Id Scheme [Type]  -- instance
	  | VarId Id Type Class
          | Application Term Term 
	  | Binding Binder [VarDecl] Term
	  | Typed Term TypeOp Type

data SigItem = AClassItem ClassItem
	     | ATypeItem TypeItem
	     | AnOpItem OpItem
