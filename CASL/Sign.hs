module CASL.Sign where

-- $Id$

import Common.Id
import Common.AS_Annotation
import FiniteMap
import Common.Lib.Graph
import Data.List(intersperse)
import Data.Maybe(mapMaybe)
import Common.GlobalAnnotations()

type SortId = Id  -- non-mixfix, but possibly compound

data FunKind = Total | Partial deriving (Show, Eq, Ord)

-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SortId], opRes :: SortId} 
	      deriving (Show, Eq, Ord)

-- we should forget about positions of "*" and "->" here to ease "deriving"
-- also: OpType will be added to Ids without explicit types
 
type PredType = [SortId]

data SymbType = OpAsItemType OpType
	      | PredType PredType
	      | Sort 
		deriving (Show, Eq, Ord)

data Symbol = Symbol {symbId :: Id, symbType :: SymbType} 
	      deriving (Show, Eq, Ord)

-- the list of items which are part of a "sort-gen" (or free type)
type GenItems = [Symbol] 

data TokenKind = Key | Comma | Semi | Less | Equal | Colon deriving (Show, Eq)

data ListPos = ListPos TokenKind Pos deriving (Show, Eq)
-- position of "," or ":"

-- full function type of a selector (result sort is component sort)
data Component = Component (Maybe Id) OpType (Maybe ListPos)
                 -- pos of "," or ":" (as Key)
		 deriving (Show, Eq) 

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id OpType [Component] [Pos] 
                 -- pos: "(", semi colons, ")", optional "?"
		 | Subsort SortId ListPos
		 -- pos of "," or "sort"
		 deriving (Show, Eq) 

-- looseness of a datatype
-- (a generated datatype will be a part of a "sort-gen")
data GenKind = Free | Generated | Loose deriving (Show, Eq)
-- for the positions of "free" and "generated" see GenItems/Sentence

data VarDecl = VarDecl { varId :: SIMPLE_ID
		       , varSort :: SortId
                       , varPos :: ListPos -- pos of "," or ":"
		       } deriving (Show, Eq)

-- sort defined as predicate subtype or as more or less loose datatype
data SortDefn = SubsortDefn VarDecl Formula [Pos]
                -- pos: "=", "{", ":", ".", "}"
              | Datatype [Annoted Alternative] GenKind GenItems [Pos]
		-- pos: "::=", "|"s 
		deriving (Show, Eq)

-- the sub- and supertypes of a sort 
data SortRels = SortRels { subsorts :: [SortId]  -- explicitely given
			 , supersorts :: [SortId] 
			 , allsubsrts :: [SortId] -- transitively closed 
			 , allsupersrts :: [SortId]
			 } deriving (Show, Eq)

emptySortRels :: SortRels
emptySortRels = SortRels [] [] [] []

data ItemPos = ItemPos String TokenKind [Pos] deriving (Show, Eq)
-- "filename" and kind of first token position

-- sort or type 
data SortItem = SortItem { sortId :: SortId
			 , sortRels :: SortRels
                         , sortDef  :: Maybe SortDefn
                         , sortPos :: ItemPos -- "sort/type", ",", "<" or "="
                         , altSorts :: [ItemPos] -- alternative positions
			 }                       -- of repeated decls
		deriving Show

instance Eq SortItem where
  (==) a b = (sortId a)==(sortId b)

data BinOpAttr = Assoc | Comm | Idem deriving (Show, Eq) 

data OpAttr = BinOpAttr BinOpAttr | UnitOpAttr Term deriving (Show, Eq)
type ConsId = Symbol

data OpDefn = OpDef [VarDecl] (Annoted Term) [Pos] 
              -- pos: "(", semicolons, ")", colon, equal
            | Constr Symbol   -- reference to sort
            | Select [ConsId] Symbol -- reference to possibly many constructors
	      deriving (Show, Eq)

data OpItem = OpItem { opId :: Id
		     , opType :: OpType
		     , opAttrs :: [OpAttr]
		     , opDefn :: Maybe OpDefn
                     , opPos :: ItemPos  -- "op" or "," 
	                      -- plus optional colon, OP_ATTR sep. by commas
		     , altOps :: [ItemPos]   
		     } deriving Show

instance Eq OpItem where
  (==) a b = ((opId a)==(opId b)) && ((opType a)==(opType b))

data PredDefn = PredDef [VarDecl] Formula [Pos] 
                -- pos: "(", semicolons, ")", "<=>"
		deriving (Show, Eq)

data PredItem = PredItem { predId :: Id
			 , predType :: PredType
			 , predDefn :: Maybe PredDefn
			 , predPos :: ItemPos -- "pred" or ","  
			 , altPreds :: [ItemPos] 
			 } deriving Show

instance Eq PredItem where
  (==) a b = ((predId a)==(predId b)) && ((predType a)==(predType b))

data TypeQualifier = OfType | AsType deriving (Show, Eq)

data Qualified = Explicit | Inferred deriving (Show, Eq)

-- a constant op has an empty list of Arguments
data Term = VarId Id SortId Qualified [Pos] 
	    -- pos: "(", var, colon, ")" (if Explicit else empty)
	  | OpAppl Id OpType [Term] Qualified [Pos]
	    -- pos: opt. "(",commas,")"
	  | Typed Term TypeQualifier SortId [Pos]
            -- pos: "as" or colon
          | Cond Term Formula Term [Pos] deriving (Show, Eq) 
            -- pos: "when", "else"

data Quantifier =  Forall | Exists | ExistsUnique deriving (Show, Eq)

data LogOp = NotOp | AndOp | OrOp | ImplOp | EquivOp | IfOp deriving (Show, Eq)

data PolyOp = DefOp | EqualOp | ExEqualOp deriving (Show, Eq)

data Formula = Quantified Quantifier [VarDecl] Formula [Pos]
	       -- pos: Quantifier, semi colons, dot
	     | Connect LogOp [Formula] [Pos]
               -- pos of (several infix) logOps
	     | TermTest PolyOp [Term] [Pos]
               -- pos of PolyOps
	     | PredAppl Id PredType [Term] Qualified [Pos]  
	       -- pos: opt. "(",commas,")"
	     | ElemTest Term SortId [Pos]
               -- pos: in
	     | FalseAtom [Pos] 
               -- pos of possible brackets
	     | TrueAtom [Pos]
               -- pos of possible brackets
	     | AnnFormula (Annoted Formula)
	       deriving (Show, Eq)

data SigItem = ASortItem (Annoted SortItem)
	     | AnOpItem (Annoted OpItem)
	     | APredItem (Annoted PredItem)
	       deriving Show

instance Eq SigItem where
  (==) (ASortItem a) (ASortItem b) = (item a)==(item b)
  (==) (AnOpItem  a) (AnOpItem  b) = (item a)==(item b)
  (==) (APredItem a) (APredItem b) = (item a)==(item b)
  (==) _ _ = False

-- lost are unused global vars
-- (and annotations for several ITEMS)

data Sign = SignAsMap { getMap   :: (FiniteMap Id [SigItem]),
                        getGraph :: (Graph SortId ()) }
	  deriving Show

instance Eq Sign where
  (==) (SignAsMap m _) (SignAsMap n _) = n==m

emptySign :: Sign
emptySign = SignAsMap emptyFM empty

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
    	         deriving (Show, Eq, Ord)

data Kind = SortKind | FunKind | PredKind
            deriving (Show, Eq, Ord)

data Axiom = AxiomDecl [VarDecl] Formula [Pos]  
	       -- pos: "var/forall", semi colons, dot
	     deriving (Show, Eq)

data Sentence = Axiom (Annoted Axiom) 
	      | GenItems GenItems [Pos] -- pos: generate/free, { , }
		deriving (Show, Eq)

getLabel :: Sentence -> String
getLabel (Axiom ax) = let annos = r_annos(ax)
                          isLbl a = case a of Label _ _ -> True; _ -> False 
                          labels = filter isLbl annos
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

data Morphism = Morphism {msource,mtarget :: Sign,
                          sort_map :: Sort_map, 
                          fun_map :: Fun_map, 
                          pred_map :: Pred_map}
                         deriving (Eq, Show)

-- ??? this needs to be implemented!
--         legal_sign :: Sign -> Bool
--         legal_morphism :: Morphism -> Bool

embedMorphism :: Sign -> Sign -> Morphism
embedMorphism a b =
  let
    l     = case a of (SignAsMap x _) -> concat $ map snd $ fmToList x
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
