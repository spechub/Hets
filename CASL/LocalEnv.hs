module LocalEnv where

-- $Header$

import Id
import AS_Annotation
import FiniteMap
import Graph
import List(intersperse)
import Maybe(mapMaybe)

type SortId = Id  -- non-mixfix, but possibly compound

data FunKind = Total | Partial deriving (Show, Eq, Ord)

-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SortId], opRes :: SortId} 
	      deriving (Show, Eq, Ord)

type PredType = [SortId]

data SymbType = OpAsItemType OpType
	      | PredType PredType
	      | Sort 
		deriving (Show, Eq, Ord)

data Symbol = Symbol {symbId :: Id, symbType :: SymbType} 
	      deriving (Show, Eq, Ord)

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) OpType [Pos] deriving (Show, Eq) 

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id OpType [Component] [Pos] 
		 | Subsort SortId [Pos]
		   deriving (Show, Eq) 

-- looseness of a datatype
-- a datatype may (only) be (sub-)part of a "sort-gen"
data GenKind = Free | Generated | Loose deriving (Show, Eq)      

data VarDecl = VarDecl {varId :: Id, varSort :: SortId} deriving (Show, Eq)

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn VarDecl Formula [Pos]
              | Datatype [Annoted Alternative] GenKind GenItems [Pos]
		deriving (Show, Eq)
-- the sub- and supertypes of a sort 
data SortRels = SortRels { subsorts :: [SortId]  -- explicitly given
			 , supersorts :: [SortId] 
			 , allsubsrts :: [SortId] -- transitively closed 
			 , allsupersrts :: [SortId]
			 } deriving (Show, Eq)

data ItemStart = Key | Comma | Semi | Less deriving (Show, Eq)

data ItemPos = ItemPos String ItemStart [Pos] deriving (Show, Eq)
-- "filename" plus positions of op, :, * ... *, ->, ",", assoc ... 

-- sort or type 
data SortItem = SortItem { sortId :: SortId
			 , sortRels :: SortRels
                         , sortDef  :: Maybe SortDefn
                         , sortPos :: ItemPos
                         , altSorts :: [ItemPos] -- alternative positions
			 }                       -- of repeated decls
		deriving (Show, Eq)

data BinOpAttr = Assoc | Comm | Idem deriving (Show, Eq) 

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term deriving (Show, Eq)
type ConsId = Symbol
type SelId = Symbol

data OpDefn = OpDef [VarDecl] (Annoted Term) [[Pos]] -- ,,,;,,,;,,,
            | Constr ConsId          -- inferred
            | Select [ConsId] SelId  -- inferred
	      deriving (Show, Eq)

data OpItem = OpItem { opId :: Id
		     , opType :: OpType
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
                     , opPos :: ItemPos      -- positions of merged attributes
		     , altOps :: [ItemPos]   -- may get lost
		     } deriving (Show, Eq)

data PredDefn = PredDef [VarDecl] Formula [[Pos]] deriving (Show, Eq)

data PredItem = PredItem { predId :: Id
			 , predType :: PredType
			 , predDefn :: Maybe PredDefn
			 , predPos :: ItemPos    
			 , altPreds :: [ItemPos] 
			 } deriving (Show, Eq)

data TypeQualifier = OfType | AsType deriving (Show, Eq)

data Qualified = Explicit | Inferred deriving (Show, Eq)

-- a constant op has an empty list of Arguments
data Term = VarId Id SortId Qualified [Pos]
	  | OpAppl Id OpType [Term] Qualified [Pos]  
	  | Typed Term TypeQualifier SortId [Pos]
          | Cond Term Formula Term [Pos] deriving (Show, Eq) 

data Quantifier =  Forall | Exists | ExistsUnique deriving (Show, Eq)

data LogOp = NotOp | AndOp | OrOp | ImplOp | EquivOp | IfOp deriving (Show, Eq)

data PolyOp = DefOp | EqualOp | ExEqualOp deriving (Show, Eq)

data Formula = Quantified Quantifier [VarDecl] Formula [[Pos]]
	     | Connect LogOp [Formula] [Pos]
	     | TermTest PolyOp [Term] [Pos]
	     | PredAppl Id PredType [Term] Qualified [Pos]  
	     | ElemTest Term SortId [Pos]
	     | FalseAtom [Pos]
	     | TrueAtom [Pos]
	     | AnnFormula (Annoted Formula)
	       deriving (Show, Eq)

data SigItem = ASortItem (Annoted SortItem)
	     | AnOpItem (Annoted OpItem)
	     | APredItem (Annoted PredItem)
	       deriving (Show, Eq)

-- lost are unused global vars
-- and annotations for several ITEMS 

data Sign = SignAsList [SigItem] deriving (Show, Eq)

data LocalEnv = SignAsMap (FiniteMap Id [SigItem]) (Graph SortId ())

instance Show LocalEnv where
    show = error "show for type LocalEnv not defined"

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
	       deriving (Show, Eq)

data Kind = SortKind | FunKind | PredKind deriving (Show, Eq)

data Axiom = AxiomDecl [VarDecl] Formula [[Pos]] -- ,,,;,,,;
	     deriving (Show, Eq)

data Sentence = Axiom (Annoted Axiom) 
	      | GenItems GenItems [Pos] -- generate/free, { , }
		deriving (Show, Eq)

getLabel :: Sentence -> String
getLabel (Axiom ax) = let annos = r_annos(ax)
                          isLabel a = case a of Label _ _ -> True; _ -> False 
                          labels = filter isLabel annos
		          getLabels(Label l _) = concat l  		    
                      in if null labels then "" else getLabels(head(labels))
getLabel (GenItems l _) = let srts = filter (\x ->
					     case x of Symbol _ Sort -> True;
                                                       _ -> False) l
                          in "ga_generated_" ++ concat 
				 (intersperse "__" 
				      (map (show . symbId) srts))

type Sort_map = FiniteMap Id Id
type Fun_map =  FiniteMap Id [(OpType, Id, Bool)] 
			{- The third field is true iff the target symbol is
                           total -}
type Pred_map = FiniteMap Id [(PredType,Id)]

--instance (Show a,Show b,Ord a) => Show (FiniteMap a b) where
--  showsPrec _ = shows . fmToList

data Morphism = Morphism {msource,mtarget :: Sign,
                          sort_map :: Sort_map, 
                          fun_map :: Fun_map, 
                          pred_map :: Pred_map}
                         deriving Eq -- (Eq,Show)

embedMorphism :: Sign -> Sign -> Morphism
embedMorphism a b =
  let
    l     = case a of (SignAsList x) -> x
    slist = map (\x -> (x,x)) $ map sortId $ map item $
            mapMaybe (\x -> case x of (ASortItem s) -> Just s;
                                                  _ -> Nothing) l
    flist = map (\x -> (opId x,[(opType x,opId x,(opKind.opType) x == Total)]))
            $ map item $ mapMaybe (\x -> case x of (AnOpItem o) -> Just o;
                                                              _ -> Nothing) l
    plist = map (\x -> (predId x,[(predType x,predId x)])) $
            map item $ mapMaybe (\x -> case x of (APredItem p) -> Just p;
                                                             _ -> Nothing) l
  in
    Morphism a b (listToFM slist) (listToFM flist) (listToFM plist)
