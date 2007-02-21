{- Collection of data structures for the Heterogeneous Tool Set
   including those for the CASL logic (but not for other logics)
-}

module AllTypes where

{-| Module      :  Data.Map

  An efficient implementation of maps from keys to values (dictionaries). 
-}

{--------------------------------------------------------------------
  Size balanced trees.
--------------------------------------------------------------------}
-- | A Map from keys @k@ and values @a@. 
data Map k a  = Tip 
              | Bin {-# UNPACK #-} !Size k a !(Map k a) !(Map k a) 

type EndoMap a = Map a a

type Size     = Int


{-| Module      :  Data.Set

  An efficient implementation of sets. 

-}

{--------------------------------------------------------------------
  Sets are size balanced trees
--------------------------------------------------------------------}
-- | A set of values @a@.
data Set a    = Tip 
              | Bin !Size a !(Set a) !(Set a) 

type Size     = Int

{- |
Module      :  $Header$
    
supply a simple data type for (precedence or subsort) relations. A
relation is conceptually a set of (ordered) pairs,
but the hidden implementation is based on a map of sets. 
An alternative view is that of a directed Graph 
without isolated nodes.

-}


data Rel a = Rel { toMap :: Map.Map a (Set.Set a) } deriving Eq
-- the invariant is that set values are never empty

{- |
Module      :  $Header$

This module supplies positions, simple and mixfix identifiers. 
A simple identifier is a lexical token given by a string and a start position.

-}

data Pos = SourcePos { sourceName :: String
                     , sourceLine :: !Int 
                     , sourceColumn :: !Int }

-- | tokens as supplied by the scanner
data Token = Token { tokStr :: String
                   , tokPos :: Pos
                   } --deriving (Show)

-- | simple ids are just tokens 
type SIMPLE_ID = Token


-- | mixfix and compound identifiers
data Id = Id [Token] [Id] [Pos] 
          -- pos of square brackets and commas of a compound list
          --deriving Show

{-| 
Module      :  $Header$

   This module provides a 'Result' type and some monadic functions
   for accumulating 'Diagnosis' messages during analysis phases.
-}


-- | severness of diagnostic messages
data DiagKind = Error | Warning | Hint | Debug 
              | MessageW -- ^ used for messages in the web interface
                deriving (Eq, Ord, Show)

-- | a diagnostic message with 'Pos'
data Diagnosis = Diag { diagKind :: DiagKind
                      , diagString :: String
                      , diagPos :: Pos 
                      } deriving Eq

-- | The result monad. A failing result should include an error message.
data Result a = Result { diags :: [Diagnosis]
                       , maybeResult :: (Maybe a)
                       } deriving (Show)


newtype IOResult a = IOResult (IO(Result a))

{- |
Module      :  $Header$

   These datastructures describe the Annotations of (Het)CASL. 
   There is also a paramterized data type for an 'Annoted' 'item'.
-}

-- | start of an annote with its WORD or a comment
data Annote_word = Annote_word String | Comment_start deriving (Show, Eq)

-- | line or group for 'Unparsed_anno' 
data Annote_text = Line_anno String | Group_anno [String] deriving (Show, Eq)

-- | formats to be displayed (may be extended in the future).
-- Drop 3 from the show result to get the string for parsing and printing  
data Display_format = DF_HTML | DF_LATEX | DF_RTF
		     deriving (Show, Eq, Ord)


-- | all possible annotations (without comment-outs)
data Annotation = -- | constructor for comments or unparsed annotes
                Unparsed_anno Annote_word Annote_text [Pos]
		-- | known annotes
		| Display_anno Id [(Display_format, String)] [Pos]
		-- postion of anno start, keywords and anno end
		| List_anno Id Id Id [Pos] 
		-- postion of anno start, commas and anno end
		| Number_anno Id [Pos] 
		-- postion of anno start, commas and anno end
		| Float_anno Id Id [Pos] 
		-- postion of anno start, commas and anno end
		| String_anno Id Id [Pos] 
		-- postion of anno start, commas and anno end
		| Prec_anno PrecRel [Id] [Id] [Pos] 
		--          ^ positions: "{",commas,"}", RecRel, "{",commas,"}"
		--          | Lower = "< "  BothDirections = "<>"
		| Assoc_anno AssocEither [Id] [Pos] -- position of commas
		| Label [String] [Pos] 
		-- postion of anno start and anno end

		-- All annotations below are only as annote line allowed
		| Semantic_anno Semantic_anno [Pos] 
		-- position information for annotations is provided 
		-- by every annotation
		  deriving (Show)



-- | an item wrapped in preceeding (left 'l_annos') 
-- and following (right 'r_annos') annotations.
-- 'opt_pos' should carry the position of an optional semicolon
-- following a formula (but is currently unused).
data Annoted a = Annoted { item :: a
			 , opt_pos :: [Pos]
			 , l_annos :: [Annotation]
                         , r_annos :: [Annotation]}
		 deriving (Show, Eq) 

-- | naming or labelling sentences
data Named s = NamedSen { senName  :: String,
                          sentence :: s }
	       deriving (Eq, Show)


{- |
Module      :  $Header$
    
   data structures for global annotations
-}

-- | all global annotations and a field for PrettyPrint stuff
data GlobalAnnos = GA { prec_annos     :: PrecedenceGraph -- ^ precedences
		      , assoc_annos    :: AssocMap  -- ^ associativity
		      , display_annos  :: DisplayMap -- ^ display annotations
		      , literal_annos  :: LiteralAnnos -- ^ literal annotations
		      , literal_map    :: LiteralMap -- ^ redundant 
			-- representation of the previous literal annotations
		      , print_conf     :: PrintConfig -- ^ gives the 
			-- possibility to print things upon position in AST
		      } deriving (Show,Eq)

-- | literal annotations for string, lists, number and floating
data LiteralAnnos = LA { string_lit :: Maybe (Id,Id)
                       , list_lit :: Map.Map Id (Id, Id)
		       , number_lit :: Maybe Id
		       , float_lit  :: Maybe (Id,Id)
		       } deriving (Show,Eq)

-- | ids to be displayed according to a format
type DisplayMap = Map.Map Id (Map.Map Display_format [Token])

-- | Options that can be set and used during PrettyPrinting
data PrintConfig = PrC { prc_inside_gen_arg :: Bool -- ^ set to True 
			 -- if inside of PARAMS or FIT_ARG
		       , prc_first_spec_in_param :: Bool 
			 -- ^ set to True when prc_inside_gen_arg is 
			 -- set to True; set to False if first spec 
			 -- is crossed
		       , prc_latex_print :: Bool
			 -- ^ True if printLatex0 is invoked
			 -- used in functions that decide on the same things 
			 -- but do different things
		       } deriving (Show,Eq)

-- | a redundant map for 'LiteralAnnos' 
type LiteralMap = Map.Map Id LiteralType

-- | description of the type of a literal for a given 'Id' in 'LiteralMap' 
data LiteralType = StringCons Id  -- ^ refer to the 'Id' of the null string 
		 | StringNull
		 | ListCons Id Id  -- ^ brackets (as 'Id') and the 'Id' of the 
                                   -- matching null list
                 | ListNull Id -- ^ brackets (as 'Id') for the empty list
		 | Number
		 | Fraction 
		 | Floating
		 | NoLiteral -- ^ and error value for a 'getLiteralType'
		   deriving (Show,Eq)

-- | a map of associative ids 
type AssocMap = Map.Map Id AssocEither

-- | a binary relation over ids as precedence graph
type PrecedenceGraph = Rel.Rel Id


{- |
Module      :  $Header$
    
    Inductive Graphs. The implementation is based on extensible finite maps.
-}


-- diagrams are just graphs
type Diagram object morphism = Graph object morphism

-- basic types
-- 
type  Node     = Int
type LNode a   = (Node,a)
type UNode     = LNode ()

type  Edge     = (Node,Node)
type LEdge b   = (Node,Node,b)
type UEdge     = LEdge ()

data Graph a b = Graph (GraphRep a b) 
type UGraph    = Graph () ()

type Path      = [Node]
type LPath a   = [LNode a]
type UPath     = [UNode]


-- types supporting inductive graph view
--
type Adj b        = [(b,Node)]
type Context a b  = (Adj b,Node,a,Adj b) 
              -- Context a b "=" Context' a b "+" Node
type MContext a b = Maybe (Context a b)
type Decomp a b   = (MContext a b,Graph a b)
type GDecomp a b  = (Context a b,Graph a b)

type UContext     = ([Node],Node,[Node])
type UDecomp      = (Maybe UContext,UGraph)


-- local
--
type Context' a b = (Adj b,a,Adj b)
type GraphRep a b = FiniteMap Node (Context' a b)


{- |
Module      :  $Header$

   This is the Abstract Syntax tree of CASL Basic_specs, Symb_items and 
   Symb_map_items.
   Follows Sect. II:2.2 of the CASL Reference Manual.
-}

data BASIC_SPEC b s f = Basic_spec [Annoted (BASIC_ITEMS b s f)]
		  deriving (Show,Eq)

data BASIC_ITEMS b s f = Sig_items (SIG_ITEMS s f)
                   -- the Annotation following the keyword is dropped
		   -- but preceding the keyword is now an Annotation allowed
		 | Free_datatype [Annoted DATATYPE_DECL] [Pos]
		   -- pos: free, type, semi colons
		 | Sort_gen [Annoted (SIG_ITEMS s f)] [Pos] 
		   -- pos: generated, opt. braces 
		 | Var_items [VAR_DECL] [Pos]
		   -- pos: var, semi colons
		 | Local_var_axioms [VAR_DECL] [Annoted (FORMULA f)] [Pos]
		   -- pos: forall, semi colons, dots
		 | Axiom_items [Annoted (FORMULA f)] [Pos]
		   -- pos: dots
                 | Ext_BASIC_ITEMS b
		   deriving (Show,Eq)

data SIG_ITEMS s f = Sort_items [Annoted (SORT_ITEM f)] [Pos] 
	         -- pos: sort, semi colons
	       | Op_items [Annoted (OP_ITEM f)] [Pos]
		 -- pos: op, semi colons
	       | Pred_items [Annoted (PRED_ITEM f)] [Pos]
		 -- pos: pred, semi colons
	       | Datatype_items [Annoted DATATYPE_DECL] [Pos]
		 -- type, semi colons
               | Ext_SIG_ITEMS s
		 deriving (Show,Eq)

data SORT_ITEM f = Sort_decl [SORT] [Pos]
	         -- pos: commas
	       | Subsort_decl [SORT] SORT [Pos]
		 -- pos: commas, <
	       | Subsort_defn SORT VAR SORT (Annoted (FORMULA f)) [Pos]
		 -- pos: "=", "{", ":", ".", "}"
		 -- the left anno list stored in Annoted Formula is 
		 -- parsed after the equal sign
	       | Iso_decl [SORT] [Pos]
	         -- pos: "="s
		 deriving (Show,Eq)

data OP_ITEM f = Op_decl [OP_NAME] OP_TYPE [OP_ATTR f] [Pos]
	       -- pos: commas, colon, OP_ATTR sep. by commas
	     | Op_defn OP_NAME OP_HEAD (Annoted (TERM f)) [Pos]
	       -- pos: "="
	       deriving (Show,Eq)

data FunKind = Total | Partial deriving (Show, Eq, Ord)

data OP_TYPE = Op_type FunKind [SORT] SORT [Pos]
	       -- pos: "*"s, "->" ; if null [SORT] then [Pos] = [] or pos: "?"
	       deriving (Show,Eq,Ord)

data OP_HEAD = Op_head FunKind [ARG_DECL] SORT [Pos]
	       -- pos: "(", semicolons, ")", colon
	       deriving (Show,Eq)

data ARG_DECL = Arg_decl [VAR] SORT [Pos]
	        -- pos: commas, colon
		deriving (Show,Eq)

data OP_ATTR f = Assoc_op_attr | Comm_op_attr | Idem_op_attr
	     | Unit_op_attr (TERM f)
	       deriving (Show,Eq)

data PRED_ITEM f = Pred_decl [PRED_NAME] PRED_TYPE [Pos]
                 -- pos: commas, colon
	       | Pred_defn PRED_NAME PRED_HEAD (Annoted (FORMULA f)) [Pos]
		 -- pos: "<=>"
		 deriving (Show,Eq)

data PRED_TYPE = Pred_type [SORT] [Pos]
	         -- pos: if null [SORT] then "(",")" else "*"s
		 deriving (Show,Eq,Ord)

data PRED_HEAD = Pred_head [ARG_DECL] [Pos]
	         -- pos: "(",semi colons , ")"
		 deriving (Show,Eq)

data DATATYPE_DECL = Datatype_decl SORT [Annoted ALTERNATIVE] [Pos] 
		     -- pos: "::=", "|"s
		     deriving (Show,Eq)

data ALTERNATIVE = Alt_construct FunKind OP_NAME [COMPONENTS] [Pos]
		   -- pos: "(", semi colons, ")" optional "?"
		 | Subsorts [SORT] [Pos]
		   -- pos: sort, commas
		   deriving (Show,Eq)

data COMPONENTS = Cons_select FunKind [OP_NAME] SORT [Pos]
                  -- pos: commas, colon or ":?"
		| Sort SORT		  
		  deriving (Show,Eq)

data VAR_DECL = Var_decl [VAR] SORT [Pos]
	        -- pos: commas, colon
		deriving (Show,Eq,Ord)

{- Position definition for FORMULA: 
   Information on parens are also encoded in [Pos].  If there
   are more Pos than necessary there is a pair of Pos enclosing the
   other Pos informations which encode the brackets of every kind
-}

{- OmDoc: FMP of type OMA, symbol (negation disjunction, etc.) applied to arguments
    quantifier with OMBIND, type of quantified variable with OMATTR
    symbols: OMS cd=CASL name=...
   theory CASL is fixed once and for all, serves as reference point (cd=CASL)
-}
data FORMULA f = Quantification QUANTIFIER [VAR_DECL] (FORMULA f) [Pos]
	       -- pos: QUANTIFIER, semi colons, dot
	     | Conjunction [FORMULA f] [Pos]
	       -- pos: "/\"s
	     | Disjunction [FORMULA f] [Pos]
	       -- pos: "\/"s
	     | Implication (FORMULA f) (FORMULA f) Bool [Pos]
	       -- pos: "=>" or "if" (True -> "=>")	   
	     | Equivalence (FORMULA f) (FORMULA f) [Pos]
	       -- pos: "<=>"
	     | Negation (FORMULA f) [Pos]
	       -- pos: not
	     | True_atom [Pos]
	       -- pos: true	    
	     | False_atom [Pos]
               -- pos: false
	     | Predication PRED_SYMB [TERM f] [Pos]
               -- pos: opt. "(",commas,")"
	     | Definedness (TERM f) [Pos]
	       -- pos: def
	     | Existl_equation (TERM f) (TERM f) [Pos]
               -- pos: =e=
	     | Strong_equation (TERM f) (TERM f) [Pos]
	       -- pos: =
	     | Membership (TERM f) SORT [Pos]
               -- pos: in
	     | Mixfix_formula (TERM f)  -- Mixfix_ Term/Token/(..)/[..]/{..}
	     -- a formula left original for mixfix analysis  -- OmDoc: not needed
	     | Unparsed_formula String [Pos]
	       -- pos: first Char in String   -- OmDoc: not needed
	     | Sort_gen_ax [Constraint] Bool -- flag: belongs to a free type?
	     | ExtFORMULA f
             -- needed for CASL extensions
	       deriving (Show,Eq,Ord)

{- In the CASL institution, sort generation constraints have an
additional signature morphism component (Sect. III:2.1.3, p.134 of the
CASL Reference Manual).  The extra signature morphism component is
needed because the naive translation of sort generation constraints
along signature morphisms may violate the satisfaction condition,
namely when sorts are identified by the translation, with the effect
that new terms can be formed. We avoid this extra component here and
instead use natural numbers to decorate sorts, in this way retaining
their identity w.r.t. the original signature. The newSort in a
Constraint is implicitly decorated with its index in the list of
Constraints. The opSymbs component collects all the operation symbols
with newSort (with that index!) as a result sort. The argument sorts
of an operation symbol are decorated explicitly via a list [Int] of
integers. The origSort in a Constraint is the original sort
corresponding to the index.  Note that this representation of sort
generation constraints is efficiently tailored towards both the use in
the proof calculus (Chap. IV:2, p. 282 of the CASL Reference Manual)
and the coding into second order logic (p. 429 of Theoret. Comp. Sci. 286). 
-}

data Constraint = Constraint { newSort :: SORT,
                               opSymbs :: [(OP_SYMB,[Int])],
                               origSort :: SORT }
                  deriving (Show,Eq,Ord)


data QUANTIFIER = Universal | Existential | Unique_existential
		  deriving (Show,Eq,Ord)

data PRED_SYMB = Pred_name PRED_NAME  -- OmDoc: similar to OP_SYMB
	       | Qual_pred_name PRED_NAME PRED_TYPE [Pos]
		 -- pos: "(", pred, colon, ")"
		 deriving (Show,Eq,Ord)

data TERM f = Simple_id SIMPLE_ID    -- "Var" might be a better constructor
                      -- OmDoc: not needed
	  | Qual_var VAR SORT [Pos]    -- OmDoc: OMV. Type of var?
	    -- pos: "(", var, colon, ")"
	  | Application OP_SYMB [TERM f] [Pos]  -- OmDoc: OMA
	    -- pos: parens around TERM f if any and seperating commas
	  | Sorted_term (TERM f) SORT [Pos] -- OmDoc: ignore
	    -- pos: colon
	  | Cast (TERM f) SORT [Pos] -- OmDoc: application of special symbol PROJ
	    -- pos: "as"
	  | Conditional (TERM f) (FORMULA f) (TERM f) [Pos]
                     -- OmDoc: application of special symobl IfThenElse
	    -- pos: "when", "else"
    -- the following are not needed in OmDoc
	  | Unparsed_term String [Pos]        -- SML-CATS

	  -- A new intermediate state
          | Mixfix_qual_pred PRED_SYMB -- as part of a mixfix formula
          | Mixfix_term [TERM f]  -- not starting with Mixfix_sorted_term/cast
	  | Mixfix_token Token   -- NO-BRACKET-TOKEN, LITERAL, PLACE
	  | Mixfix_sorted_term SORT [Pos]
	    -- pos: colon
	  | Mixfix_cast SORT [Pos]
	    -- pos: "as" 
          | Mixfix_parenthesized [TERM f] [Pos]  -- non-emtpy term list
	    -- pos: "(", commas, ")" 
          | Mixfix_bracketed [TERM f] [Pos]
	    -- pos: "[", commas, "]" 
          | Mixfix_braced [TERM f] [Pos]         -- also for list-notation 
	    -- pos: "{", "}" 
	    deriving (Show,Eq,Ord)

data OP_SYMB = Op_name OP_NAME   -- OmDoc: not needed
	     | Qual_op_name OP_NAME OP_TYPE [Pos]  -- OmDoc: OMS
                    -- problem: CASL overloading! extend OmDoc? or disambiguate name?
		 -- pos: "(", op, colon, ")"
	       deriving (Show,Eq,Ord)

type OP_NAME = Id

type PRED_NAME = Id

type SORT = Id

type VAR = SIMPLE_ID

----- 
data SYMB_ITEMS = Symb_items SYMB_KIND [SYMB] [Pos] 
		  -- pos: SYMB_KIND, commas
		  deriving (Show,Eq)

data SYMB_ITEMS_LIST = Symb_items_list [SYMB_ITEMS] [Pos] 
		  -- pos: commas
		  deriving (Show,Eq)

data SYMB_MAP_ITEMS = Symb_map_items SYMB_KIND [SYMB_OR_MAP] [Pos]
		      -- pos: SYMB_KIND, commas
		      deriving (Show,Eq)

data SYMB_MAP_ITEMS_LIST = Symb_map_items_list [SYMB_MAP_ITEMS] [Pos] 
		  -- pos: commas
		  deriving (Show,Eq)

data SYMB_KIND = Implicit | Sorts_kind 
	       | Ops_kind | Preds_kind
		 deriving (Show,Eq)

data SYMB = Symb_id Id
	  | Qual_id Id TYPE [Pos] 
	    -- pos: colon
	    deriving (Show,Eq)

data TYPE = O_type OP_TYPE
	  | P_type PRED_TYPE
	  | A_type SORT -- ambiguous pred or (constant total) op 
	    deriving (Show,Eq)

data SYMB_OR_MAP = Symb SYMB
		 | Symb_map SYMB SYMB [Pos]
		   -- pos: "|->"
		   deriving (Show,Eq)


{- |
Module      :  $Header$

CASL signature
    
-}


-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SORT], opRes :: SORT} 
              deriving (Show, Eq, Ord)

data PredType = PredType {predArgs :: [SORT]} deriving (Show, Eq, Ord)

type OpMap = Map.Map Id (Set.Set OpType)

-- OmDoc: theory, with set of symbols
data Sign f e = Sign { sortSet :: Set.Set SORT  -- OmDoc: type symbols
               , sortRel :: Rel.Rel SORT  
                             -- OmDoc: injection object sybmols, e.g. g__injNatInt
               , opMap :: OpMap -- OmDoc: object symbols
               , assocOps :: OpMap -- OmDoc: ignore
               , predMap :: Map.Map Id (Set.Set PredType) -- OmDoc: object symbols
               , varMap :: Map.Map SIMPLE_ID (Set.Set SORT) -- OmDoc: ignore
               , sentences :: [Named (FORMULA f)]  -- OmDoc: ignore
               , envDiags :: [Diagnosis] -- OmDoc: ignore
               , extendedInfo :: e -- see CoCASL, ModalCASL (later on)
               } deriving Show

{- |
Module      :  $Header$
    
Symbols and signature morphisms for the CASL logic
-}


data SymbType = OpAsItemType OpType
                -- since symbols do not speak about totality, the totality
                -- information in OpType has to be ignored
              | PredAsItemType PredType
              | SortAsItemType 
                deriving (Show)

data Symbol = Symbol {symName :: Id, symbType :: SymbType} 
              deriving (Show, Eq, Ord)

type SymbolSet = Set.Set Symbol 
type SymbolMap = Map.Map Symbol Symbol 

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId Kind Id
                 deriving (Show, Eq, Ord)

type RawSymbolSet = Set.Set RawSymbol 
type RawSymbolMap = Map.Map RawSymbol RawSymbol 

data Kind = SortKind | FunKind | PredKind
            deriving (Show, Eq, Ord)

type Sort_map = Map.Map SORT SORT
-- allways use the partial profile as key! 
type Fun_map =  Map.Map (Id,OpType) (Id, FunKind)
type Pred_map = Map.Map (Id,PredType) Id

-- OmDoc Morphism
data Morphism f e m = Morphism {msource :: Sign f e, 
                          mtarget :: Sign f e,
                          sort_map :: Sort_map, -- OmDoc: value,value pairs
                          fun_map :: Fun_map,  -- OmDoc: value,value pairs
                          pred_map :: Pred_map, -- OmDoc: value,value pairs
                          extended_map :: m}
                         deriving (Eq, Show)

type Ext f e m = Sign f e -> Sign f e -> m

{- |

Module      :  $Header$

  This module provides the sublogic functions (as required by Logic.hs)
  for CASL. The functions allow to compute the minimal sublogics needed
  by a given element, to check whether an item is part of a given
  sublogic, and to project an element into a given sublogic.

------------------------------------------------------------------------------
-- | Datatypes for CASL sublogics
------------------------------------------------------------------------------

data CASL_Formulas = Atomic  -- ^ atomic logic
                   | Horn    -- ^ positive conditional logic
                   | GHorn   -- ^ generalized positive conditional logic
                   | FOL     -- ^ first-order logic
                   deriving (Show,Ord,Eq)

data CASL_Sublogics = CASL_SL
                      { has_sub::Bool,   -- ^ subsorting
                        has_part::Bool,  -- ^ partiality
                        has_cons::Bool,  -- ^ sort generation contraints
                        has_eq::Bool,    -- ^ equality
                        has_pred::Bool,  -- ^ predicates
                        which_logic::CASL_Formulas
                      } deriving (Show,Eq)

-}

{- |
Module      :  $Header$

   Here is the place where the class Logic is instantiated for CASL.
   Also the instances for Syntax an Category.
-}


data CASL = CASL deriving Show

type CASLBasicSpec = BASIC_SPEC () () ()
type CASLFORMULA = FORMULA ()
-- Following types are imported from CASL.Amalgamability:
type CASLSign = Sign () ()
type CASLMor = Morphism () () ()

{-| 
Module      :  $Header$

   These data structures describe the abstract syntax tree for heterogenous 
   structured specifications in HetCASL.
   Follows Sect. II:2.2.3 of the CASL Reference Manual.

-}

data SPEC = Basic_spec G_basic_spec 
	  | Translation (Annoted SPEC) RENAMING 
	  | Reduction (Annoted SPEC) RESTRICTION 
	  | Union [(Annoted SPEC)] [Pos]
	    -- pos: "and"s
	  | Extension [(Annoted SPEC)] [Pos]
	    -- pos: "then"s
	  | Free_spec (Annoted SPEC) [Pos]
	    -- pos: "free"
	  | Cofree_spec (Annoted SPEC) [Pos]
	    -- pos: "cofree"
	  | Local_spec (Annoted SPEC) (Annoted SPEC) [Pos]
	    -- pos: "local", "within"
	  | Closed_spec (Annoted SPEC) [Pos]
	    -- pos: "closed"
          | Group (Annoted SPEC) [Pos]
	    -- pos: "{","}"
          | Spec_inst SPEC_NAME [Annoted FIT_ARG] [Pos]
	    -- pos: many of "[","]"; one balanced pair per FIT_ARG
	  | Qualified_spec Logic_name (Annoted SPEC) [Pos]
	    -- pos: "logic", Logic_name,":"
          | Data AnyLogic AnyLogic (Annoted SPEC) (Annoted SPEC) [Pos]
            -- pos: "data"
	    deriving (Show)


{- Renaming and Hiding can be performend with intermediate Logic
   mappings / Logic projections.

-}
data RENAMING = Renaming [G_mapping] [Pos]
	        -- pos: "with", list of comma pos 
		 deriving (Show,Eq)

data RESTRICTION = Hidden [G_hiding] [Pos]
		   -- pos: "hide", list of comma pos 
		 | Revealed G_symb_map_items_list [Pos]
		   -- pos: "reveal", list of comma pos 
		   deriving (Show,Eq)

data G_mapping = G_symb_map G_symb_map_items_list
	       | G_logic_translation Logic_code
		 deriving (Show,Eq)

data G_hiding = G_symb_list G_symb_items_list
	       | G_logic_projection Logic_code
		 deriving (Show,Eq)

data SPEC_DEFN = Spec_defn SPEC_NAME GENERICITY (Annoted SPEC) [Pos]
	         -- pos: "spec","=",opt "end"
		 deriving (Show)

data GENERICITY = Genericity PARAMS IMPORTED [Pos]
		  -- pos: many of "[","]" opt ("given", commas) 
		  deriving (Show)

data PARAMS = Params [Annoted SPEC]
	      deriving (Show)

data IMPORTED = Imported [Annoted SPEC]
		deriving (Show)

data FIT_ARG = Fit_spec (Annoted SPEC) G_symb_map_items_list [Pos]
	       -- pos: opt "fit"
	     | Fit_view VIEW_NAME [Annoted FIT_ARG] [Pos] [Annotation]
	       -- The list of Annotations is written before the keyword 'view'
	       -- pos: "view", opt many of "[","]"
	       deriving (Show)

data VIEW_DEFN = View_defn VIEW_NAME GENERICITY VIEW_TYPE
			   [G_mapping] [Pos]
	         -- pos: "view",":",opt "=", opt "end" 
		  deriving (Show)

data VIEW_TYPE = View_type (Annoted SPEC) (Annoted SPEC) [Pos]
	         -- pos: "to"
		 deriving (Show)

type SPEC_NAME = SIMPLE_ID
type VIEW_NAME = SIMPLE_ID

data Logic_code = Logic_code (Maybe Token) 
                             (Maybe Logic_name) 
			     (Maybe Logic_name) [Pos]
		 -- pos: "logic",<encoding>,":",<src-logic>,"->",<targ-logic>
                 -- one of <encoding>, <src-logic> or <targ-logic>
                 -- must be given (by Just)
                 -- "logic bla"    => <encoding> only 
                 -- "logic bla ->" => <src-logic> only
                 -- "logic -> bla" => <targ-logic> only
                 -- "logic bla1 -> bla2" => <src-logic> and <targ-logic>
                 -- -- "logic bla1:bla2"    => <encoding> and <src-logic>
                 -- ^ this notation is not very useful and is not maintained
                 -- "logic bla1:bla2 ->" => <encoding> and <src-logic> (!)
                 -- "logic bla1: ->bla2" => <encoding> and <targ-logic>
		  deriving (Show,Eq)

data Logic_name = Logic_name Token (Maybe Token)
		  deriving (Show,Eq)

{-| 
Module      :  $Header$

   These data structures describe the abstract syntax tree for heterogenous 
   architectural specifications in HetCASL.
   Follows Sect. II:2.2.4 of the CASL Reference Manual.
-}


data ARCH_SPEC_DEFN = Arch_spec_defn ARCH_SPEC_NAME (Annoted ARCH_SPEC) [Pos]
		      -- pos: "arch","spec","=",opt "end"
		      deriving (Show)

data ARCH_SPEC = Basic_arch_spec [Annoted UNIT_DECL_DEFN]
		                 (Annoted UNIT_EXPRESSION) [Pos]
	         -- pos: "unit","result"
	       | Arch_spec_name ARCH_SPEC_NAME
	       | Group_arch_spec (Annoted ARCH_SPEC) [Pos]
		 -- pos: "{","}"
		 deriving (Show)


data UNIT_DECL_DEFN = Unit_decl UNIT_NAME REF_SPEC [Annoted UNIT_TERM] [Pos]
                      -- pos: ":", opt ("given"; Annoted holds pos of commas)
                    | Unit_defn UNIT_NAME UNIT_EXPRESSION [Pos]
                      -- pos: "="
                      deriving (Show)

data UNIT_SPEC_DEFN = Unit_spec_defn SPEC_NAME UNIT_SPEC [Pos]
		      -- pos: "unit","spec","=", opt "end"
		      deriving (Show)

data UNIT_SPEC = Unit_type [Annoted SPEC] (Annoted SPEC) [Pos]
	         -- pos: opt "*"s , "->"
	       | Spec_name SPEC_NAME
	       | Closed_unit_spec UNIT_SPEC [Pos]
		 -- pos: "closed"
		 deriving (Show)

data REF_SPEC = Unit_spec UNIT_SPEC
              | Refinement Bool UNIT_SPEC [G_mapping] REF_SPEC [Pos]
                -- false means "behaviourally"
	      | Arch_unit_spec (Annoted ARCH_SPEC) [Pos] 
		 -- pos: "arch","spec"
		 -- The ARCH_SPEC has to be surrounded with braces and
		 -- after the opening brace is a [Annotation] allowed
	      | Compose_ref [REF_SPEC] [Pos]
		 -- pos: "then"
              | Component_ref [UNIT_REF] [Pos]
                -- pos "{", commas and "}"
		 deriving (Show)

data UNIT_REF = Unit_ref UNIT_NAME REF_SPEC [Pos] 
		 -- pos: ":"
                 deriving (Show)

data UNIT_EXPRESSION = Unit_expression [UNIT_BINDING] (Annoted UNIT_TERM) [Pos]
		       -- pos: opt "lambda",semi colons, "."
		       deriving (Show)

data UNIT_BINDING = Unit_binding UNIT_NAME UNIT_SPEC [Pos]
		    -- pos: ":"
		    deriving (Show) 

data UNIT_TERM = Unit_reduction (Annoted UNIT_TERM) RESTRICTION
	       | Unit_translation (Annoted UNIT_TERM) RENAMING 
	       | Amalgamation [Annoted UNIT_TERM] [Pos]
		 -- pos: "and"s
	       | Local_unit [Annoted UNIT_DECL_DEFN] (Annoted UNIT_TERM) [Pos] 
		 -- pos: "local", "within"
	       | Unit_appl UNIT_NAME [FIT_ARG_UNIT] [Pos]
		 -- pos: many of "[","]"
	       | Group_unit_term (Annoted UNIT_TERM) [Pos]
		 -- pos: "{","}"
		 deriving (Show)

data FIT_ARG_UNIT = Fit_arg_unit (Annoted UNIT_TERM) [G_mapping] [Pos] 
		    -- pos: opt "fit"
		    deriving (Show)

type ARCH_SPEC_NAME = SIMPLE_ID
type UNIT_NAME = SIMPLE_ID
{-| 
   
Module      :  $Header$

   These data structures describe the abstract syntax tree for heterogenous 
   libraries in HetCASL.
   Follows Sect. II:2.2.5 of the CASL Reference Manual.

-}

data LIB_DEFN = Lib_defn LIB_NAME [Annoted LIB_ITEM] [Pos] [Annotation]
	        -- pos: "library"
	        -- list of annotations is parsed preceding the first LIB_ITEM
	        -- the last LIB_ITEM may be annotated with a following comment
	        -- the first LIB_ITEM cannot be annotated
		deriving (Show)

{- for information on the list of Pos see the documentation in
   AS_Structured.hs and AS_Architecture.hs -}

data LIB_ITEM = Spec_defn Syntax.AS_Structured.SPEC_NAME 
		          Syntax.AS_Structured.GENERICITY 
                          (Annoted Syntax.AS_Structured.SPEC) 
			  [Pos]
	      
	      | View_defn Syntax.AS_Structured.VIEW_NAME 
		          Syntax.AS_Structured.GENERICITY 
			  Syntax.AS_Structured.VIEW_TYPE 
			  [Syntax.AS_Structured.G_mapping]
			  [Pos]

	      | Arch_spec_defn Syntax.AS_Architecture.ARCH_SPEC_NAME 
		               (Annoted Syntax.AS_Architecture.ARCH_SPEC) 
			       [Pos]

	      | Unit_spec_defn Syntax.AS_Structured.SPEC_NAME 
		               Syntax.AS_Architecture.UNIT_SPEC 
			       [Pos]

	      | Ref_spec_defn Syntax.AS_Structured.SPEC_NAME 
		               Syntax.AS_Architecture.REF_SPEC 
			       [Pos]

	      | Download_items  LIB_NAME [ITEM_NAME_OR_MAP] [Pos] 
		-- pos: "from","get",commas, opt "end"
	      | Logic_decl Syntax.AS_Structured.Logic_name [Pos]
		-- pos:  "logic", Logic_name
		deriving (Show)

data ITEM_NAME_OR_MAP = Item_name ITEM_NAME 
		      | Item_name_map ITEM_NAME ITEM_NAME [Pos]
			-- pos: "|->"
			deriving (Show,Eq)

type ITEM_NAME = SIMPLE_ID

data LIB_NAME = Lib_version LIB_ID VERSION_NUMBER
	      | Lib_id LIB_ID

data LIB_ID = Direct_link URL [Pos]
	      -- pos: start of URL
	    | Indirect_link PATH [Pos]
	      -- pos: start of PATH



data VERSION_NUMBER = Version_number [String] [Pos]
		      -- pos: "version", start of first string
		      deriving (Show,Eq) 

type URL = String
type PATH = String

{-| 
   
Module      :  $Header$

   Provide prover stuff for class Logic.Sentences

-}


-- theories and theory morphisms

type Theory sign sen = (sign,[Named sen])

data TheoryMorphism sign sen mor = 
     TheoryMorphism {t_source, t_target :: Theory sign sen,
                     t_morphism :: mor
                    } 

-- proofs and provers

type Rule = String

type Tactic_script = String  -- the file name

data Proof_status proof_tree = Open String
                      | Disproved String 
                      | Proved(String,
                               [String], -- used axioms
                               String, -- name of prover
                               proof_tree,
                               Tactic_script)
                      | Consistent Tactic_script
     deriving (Eq, Show, Read)

data Prover sign sen proof_tree symbol = 
     Prover { prover_name :: String,
              prover_sublogic :: String,
              prove :: String -> (sign, [Named sen]) -> [Named sen] 
                         -> IO([Proof_status proof_tree])
                 -- input: theory name, theory, goals
                 -- output: proof status for goals and lemmas
            }

{- possibly needed in the future
              add_sym :: symbol -> IO(Bool),  -- returns True if succeeded
              remove_sym :: symbol -> IO(Bool), -- returns True if succeeded
              add_sen :: sen -> IO(Bool),  -- returns True if succeeded
              remove_sen :: sen -> IO(Bool), -- returns True if succeeded
              add_termination_info :: [symbol] -> [(symbol,[symbol])] -> IO(Bool), -- returns True if succeeded
              remove_termination_info :: [symbol] -> [(symbol,[symbol])] -> IO(Bool), -- returns True if succeeded
              replay :: proof_tree -> Maybe sen -- what about the theory???
-}

data ConsChecker sign sentence morphism proof_tree = 
 ConsChecker { 
   cons_checker_name :: String,
   cons_checker_sublogic :: String,
   cons_check :: String -> TheoryMorphism sign sentence morphism 
                 -- name of target theory, theory extension
                        -> IO([Proof_status proof_tree])
  }

{- |
Module      :  $Header$

-- languages, define like "data CASL = CASL deriving Show" 
-}

class Show lid => Language lid where
    language_name :: lid -> String
    language_name i = show i
    description :: lid -> String
    -- default implementation
    description _ = "No description available"

{- |
Module      :  $Header$
 
   Provides data structures for logics (with symbols). Logics are
   a type class with an "identitiy" type (usually interpreted
   by a singleton set) which serves to treat logics as 
   data. All the functions in the type class take the
   identity as first argument in order to determine the logic.

-}


class (PrintLaTeX a, Typeable a, ATermConvertible a) => PrintTypeConv a
class (Eq a, PrintTypeConv a) => EqPrintTypeConv a

class (Language lid, Eq sign, Eq morphism)
    => Category lid sign morphism | lid -> sign, lid -> morphism where
         ide :: lid -> sign -> morphism
         comp :: lid -> morphism -> morphism -> Result morphism
           -- diagrammatic order
         dom, cod :: lid -> morphism -> sign
         legal_obj :: lid -> sign -> Bool
         legal_mor :: lid -> morphism -> Bool

-- abstract syntax, parsing and printing

class (Language lid, PrintTypeConv basic_spec, 
       EqPrintTypeConv symb_items, 
       EqPrintTypeConv symb_map_items) 
    => Syntax lid basic_spec symb_items symb_map_items
        | lid -> basic_spec, lid -> symb_items,
          lid -> symb_map_items
      where 
         -- parsing
         parse_basic_spec :: lid -> Maybe(AParser st basic_spec)
         parse_symb_items :: lid -> Maybe(AParser st symb_items)
         parse_symb_map_items :: lid -> Maybe(AParser st symb_map_items)
         -- default implementations
         parse_basic_spec _ = Nothing
         parse_symb_items _ = Nothing
         parse_symb_map_items _ = Nothing

-- sentences (plus prover stuff and "symbol" with "Ord" for efficient lookup)

class (Category lid sign morphism, Ord sentence,
       Ord symbol, 
       PrintTypeConv sign, PrintTypeConv morphism,
       PrintTypeConv sentence, PrintTypeConv symbol,
       Eq proof_tree, Show proof_tree, ATermConvertible proof_tree, 
       Typeable proof_tree)
    => Sentences lid sentence proof_tree sign morphism symbol
        | lid -> sentence, lid -> sign, lid -> morphism,
          lid -> symbol, lid -> proof_tree
      where
         -- sentence translation
      map_sen :: lid -> morphism -> sentence -> Result sentence
      map_sen l _ _ = statErr l "map_sen"
         -- simplification of sentences (leave out qualifications)
      simplify_sen :: lid -> sign -> sentence -> sentence
      simplify_sen _ _ = id  -- default implementation
         -- parsing of sentences
      parse_sentence :: lid -> Maybe (AParser st sentence)
      parse_sentence _ = Nothing
           -- print a sentence with comments
      print_named :: lid -> GlobalAnnos -> Named sentence -> Doc
      print_named _ = printText0
      sym_of :: lid -> sign -> Set symbol
      symmap_of :: lid -> morphism -> EndoMap symbol
      sym_name :: lid -> symbol -> Id 
      provers :: lid -> [Prover sign sentence proof_tree symbol]
      provers _ = []
      cons_checkers :: lid -> [ConsChecker sign sentence morphism proof_tree] 
      cons_checkers _ = []
      consCheck :: lid -> Theory sign sentence -> 
                       morphism -> [Named sentence] -> Result (Maybe Bool)
      consCheck l _ _ _ = statErr l "consCheck"

-- static analysis

class ( Syntax lid basic_spec symb_items symb_map_items
      , Sentences lid sentence proof_tree sign morphism symbol
      , Ord raw_symbol, PrintLaTeX raw_symbol, Typeable raw_symbol)
    => StaticAnalysis lid 
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol 
        | lid -> basic_spec, lid -> sentence, lid -> symb_items,
          lid -> symb_map_items, lid -> proof_tree,
          lid -> sign, lid -> morphism, lid -> symbol, lid -> raw_symbol
      where
         -- static analysis of basic specifications and symbol maps
         basic_analysis :: lid -> 
                           Maybe((basic_spec,  -- abstract syntax tree
                            sign,   -- efficient table for env signature
                            GlobalAnnos) ->   -- global annotations
                           Result (basic_spec,sign,sign,[Named sentence]))
                           -- the resulting bspec has analyzed axioms in it
                           -- sign's: sigma_local, sigma_complete, i.e.
                           -- the second output sign united with the input sign
                           -- should yield the first output sign
                           -- the second output sign is the accumulated sign
         -- default implementation
         basic_analysis _ = Nothing

         -- Shouldn't the following deliver Maybes???
         sign_to_basic_spec :: lid -> sign -> [Named sentence] -> basic_spec
         stat_symb_map_items :: 
             lid -> [symb_map_items] -> Result (EndoMap raw_symbol)
         stat_symb_map_items _ _ = fail "Logic.stat_symb_map_items"     
         stat_symb_items :: lid -> [symb_items] -> Result [raw_symbol] 
         stat_symb_items l _ = statErr l "stat_symb_items"
         -- amalgamation
         weaklyAmalgamableCocone :: lid -> Diagram sign morphism 
                                     -> Result (sign, Map Node morphism)
         weaklyAmalgamableCocone l _ = statErr l "weaklyAmalgamableCocone"
         -- architectural sharing analysis
         ensures_amalgamability :: lid ->
              ([CASLAmalgOpt],        -- the program options
               Diagram sign morphism, -- the diagram to be analyzed
               [(Node, morphism)],    -- the sink
               Diagram String String) -- the descriptions of nodes and edges
                  -> Result Amalgamates
         ensures_amalgamability l _ = statErr l "ensures_amalgamability"
         -- symbols and symbol maps
         symbol_to_raw :: lid -> symbol -> raw_symbol
         id_to_raw :: lid -> Id -> raw_symbol 
         matches :: lid -> symbol -> raw_symbol -> Bool
   
         -- operations on signatures and morphisms
         empty_signature :: lid -> sign
         signature_union :: lid -> sign -> sign -> Result sign
         signature_union l _ _ = statErr l "signature_union"
         morphism_union :: lid -> morphism -> morphism -> Result morphism
         morphism_union l _ _ = statErr l "morphism_union"
         final_union :: lid -> sign -> sign -> Result sign
         final_union l _ _ = statErr l "final_union"
           -- see CASL reference manual, III.4.1.2
         is_subsig :: lid -> sign -> sign -> Bool
         inclusion :: lid -> sign -> sign -> Result morphism
         inclusion l _ _ = statErr l "inclusion"
         generated_sign, cogenerated_sign :: 
             lid -> Set symbol -> sign -> Result morphism
         generated_sign l _ _ = statErr l "generated_sign"
         cogenerated_sign l _ _ = statErr l "cogenerated_sign"
         induced_from_morphism :: 
             lid -> EndoMap raw_symbol -> sign -> Result morphism
         induced_from_morphism l _ _ = statErr l "induced_from_morphism"
         induced_from_to_morphism :: 
             lid -> EndoMap raw_symbol -> sign -> sign -> Result morphism
         induced_from_to_morphism l _ _ _ = 
             statErr l "induced_from_to_morphism"
	 -- generate taxonomy from theory
	 theory_to_taxonomy :: lid 
			    -> TaxoGraphKind
			    -> MMiSSOntology
			    -> sign -> [Named sentence] 
			    -> Result MMiSSOntology
	 theory_to_taxonomy l _ _ _ _ = statErr l "theory_to_taxonomy"

-- sublogics

class (Ord l, Show l) => LatticeWithTop l where
  meet, join :: l -> l -> l
  top :: l


-- logics

class (StaticAnalysis lid 
        basic_spec sentence proof_tree symb_items symb_map_items
        sign morphism symbol raw_symbol,
       LatticeWithTop sublogics, ATermConvertible sublogics,
       Typeable sublogics) 
    => Logic lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree
        | lid -> sublogics, lid -> basic_spec, lid -> sentence, 
          lid -> symb_items, lid -> symb_map_items, lid -> proof_tree,
          lid -> sign, lid -> morphism, lid ->symbol, lid -> raw_symbol
          where

         -- for a process logic, return its data logic
         data_logic :: lid -> Maybe AnyLogic
         data_logic _ = Nothing

         sublogic_names :: lid -> sublogics -> [String] 
         sublogic_names lid _ = [language_name lid]
             -- the first name is the principal name
         all_sublogics :: lid -> [sublogics]
         all_sublogics _ = [top]

         is_in_basic_spec :: lid -> sublogics -> basic_spec -> Bool
         is_in_basic_spec _ _ _ = False
         is_in_sentence :: lid -> sublogics -> sentence -> Bool
         is_in_sentence _ _ _ = False
         is_in_symb_items :: lid -> sublogics -> symb_items -> Bool
         is_in_symb_items _ _ _ = False
         is_in_symb_map_items :: lid -> sublogics -> symb_map_items -> Bool
         is_in_symb_map_items _ _ _ = False
         is_in_sign :: lid -> sublogics -> sign -> Bool
         is_in_sign _ _ _ = False
         is_in_morphism :: lid -> sublogics -> morphism -> Bool
         is_in_morphism _ _ _ = False
         is_in_symbol :: lid -> sublogics -> symbol -> Bool
         is_in_symbol _ _ _ = False
 
         min_sublogic_basic_spec :: lid -> basic_spec -> sublogics
         min_sublogic_basic_spec _ _ = top
         min_sublogic_sentence :: lid -> sentence -> sublogics
         min_sublogic_sentence _ _ = top
         min_sublogic_symb_items :: lid -> symb_items -> sublogics
         min_sublogic_symb_items _ _ = top
         min_sublogic_symb_map_items :: lid -> symb_map_items -> sublogics
         min_sublogic_symb_map_items _ _ = top
         min_sublogic_sign :: lid -> sign -> sublogics
         min_sublogic_sign _ _ = top
         min_sublogic_morphism :: lid -> morphism -> sublogics
         min_sublogic_morphism _ _ = top
         min_sublogic_symbol :: lid -> symbol -> sublogics
         min_sublogic_symbol _ _ = top
         proj_sublogic_basic_spec :: lid -> sublogics 
                                  -> basic_spec -> basic_spec
         proj_sublogic_basic_spec _ _ b = b                          
         proj_sublogic_symb_items :: lid -> sublogics 
                                  -> symb_items -> Maybe symb_items
         proj_sublogic_symb_items _ _ _ = Nothing
         proj_sublogic_symb_map_items :: lid -> sublogics 
                                      -> symb_map_items -> Maybe symb_map_items
         proj_sublogic_symb_map_items _ _ _ = Nothing
         proj_sublogic_sign :: lid -> sublogics -> sign -> sign 
         proj_sublogic_sign _ _ s = s
         proj_sublogic_morphism :: lid -> sublogics -> morphism -> morphism
         proj_sublogic_morphism _ _ m = m
         proj_sublogic_epsilon :: lid -> sublogics -> sign -> morphism
         proj_sublogic_epsilon li _ s = ide li s
         proj_sublogic_symbol :: lid -> sublogics -> symbol -> Maybe symbol
         proj_sublogic_symbol _ _ _ = Nothing

         top_sublogic :: lid -> sublogics
         top_sublogic _ = top

 
----------------------------------------------------------------
-- Existential type covering any logic
----------------------------------------------------------------

data AnyLogic = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
        sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree =>
        Logic lid


{- class hierarchy:
                            Language
               __________/     
   Category
      |                  /       
   Sentences      Syntax
      \            /
      StaticAnalysis (no sublogics)
            \                        
             \                             
            Logic

-}

{-| 
   
Module      :  $Header$
   
   Provides data structures for institution comorphisms. 
   These are just collections of
   functions between (some of) the types of logics.

-}

class (Language cid,
       Logic lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1,
       Logic lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2) =>
  Comorphism cid
            lid1 sublogics1 basic_spec1 sentence1 symb_items1 symb_map_items1
                sign1 morphism1 symbol1 raw_symbol1 proof_tree1
            lid2 sublogics2 basic_spec2 sentence2 symb_items2 symb_map_items2
                sign2 morphism2 symbol2 raw_symbol2 proof_tree2
             | cid -> lid1, cid -> lid2

  where
    -- source and target logic and sublogic
    -- the source sublogic is the maximal one for which the comorphism works
    -- the target sublogic is the resulting one
    sourceLogic :: cid -> lid1
    sourceSublogic :: cid -> sublogics1
    targetLogic :: cid -> lid2
    targetSublogic :: cid -> sublogics2
    -- finer information of target sublogics corresponding to source sublogics
    mapSublogic :: cid -> sublogics1 -> sublogics2
    -- default implementation
    mapSublogic cid _ = targetSublogic cid
    -- the translation functions are partial 
    -- because the target may be a sublanguage
    -- map_basic_spec :: cid -> basic_spec1 -> Result basic_spec2
    -- cover theoroidal comorphisms as well
    map_theory :: cid -> (sign1,[Named sentence1])
                      -> Result (sign2,[Named sentence2])
    map_morphism :: cid -> morphism1 -> Result morphism2
    map_sentence :: cid -> sign1 -> sentence1 -> Result sentence2
          -- also covers semi-comorphisms
          -- with no sentence translation
          -- - but these are spans!
    map_symbol :: cid -> symbol1 -> Set symbol2
    constituents :: cid -> [String]
    -- default implementation
    constituents cid = [language_name cid]


data IdComorphism lid sublogics = 
     IdComorphism lid sublogics 


data CompComorphism cid1 cid2 = CompComorphism cid1 cid2 deriving Show


{- |
Module      :  $Header$
   
   The Grothendieck logic is defined to be the
   heterogeneous logic over the logic graph.
   This will be the logic over which the data 
   structures and algorithms for specification in-the-large
   are built.

-}


------------------------------------------------------------------
--"Grothendieck" versions of the various parts of type class Logic
------------------------------------------------------------------

-- | Grothendieck basic specifications
data G_basic_spec = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_basic_spec lid basic_spec 

-- | Grothendieck sentences
data G_sentence = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sentence lid sentence 


-- | Grothendieck sentence lists
data G_l_sentence_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
  G_l_sentence_list lid [Named sentence] 

-- | Grothendieck signatures
data G_sign = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sign lid sign -- OmDoc: lid leads to cd, sign leads to list of symbols


-- | Grothendieck signature lists
data G_sign_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_sign_list lid [sign] 

-- | Grothendieck extended signatures
data G_ext_sign = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_ext_sign lid sign (Set.Set symbol)


-- | Grothendieck theories
data G_theory = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
  G_theory lid sign [Named sentence]


-- | Grothendieck symbols
data G_symbol = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
  G_symbol lid symbol 

-- | Grothendieck symbol lists
data G_symb_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_symb_items_list lid [symb_items] 

-- | Grothendieck symbol maps
data G_symb_map_items_list = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_symb_map_items_list lid [symb_map_items] 

-- | Grothendieck diagrams
data G_diagram = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree  =>
        G_diagram lid (Diagram sign morphism) 

-- | Grothendieck sublogics
data G_sublogics = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_sublogics lid sublogics 

-- | Homogeneous Grothendieck signature morphisms
data G_morphism = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        G_morphism lid morphism

----------------------------------------------------------------
-- Existential types for the logic graph
----------------------------------------------------------------

-- | Existential type for comorphisms
data AnyComorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Comorphism cid 
                 lid1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      Comorphism cid


-- | Logic graph
data LogicGraph = LogicGraph {
                    logics :: Map.Map String AnyLogic, 
                    comorphisms :: Map.Map String AnyComorphism,
                    inclusions :: Map.Map (String,String) AnyComorphism,
                    unions :: Map.Map (String,String) (AnyComorphism,AnyComorphism)
                  }


-- | auxiliary existential type needed for composition of comorphisms
data AnyComorphismAux lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 = 
        forall cid .
      Comorphism cid 
                 lid1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
      ComorphismAux cid lid1 lid2 sign1 morphism2


------------------------------------------------------------------
-- The Grothendieck signature category
------------------------------------------------------------------

-- | Grothendieck signature morphisms
data GMorphism = forall cid lid1 sublogics1
        basic_spec1 sentence1 symb_items1 symb_map_items1
        sign1 morphism1 symbol1 raw_symbol1 proof_tree1
        lid2 sublogics2
        basic_spec2 sentence2 symb_items2 symb_map_items2 
        sign2 morphism2 symbol2 raw_symbol2 proof_tree2 .
      Comorphism cid 
                 lid1 sublogics1 basic_spec1 sentence1 
                 symb_items1 symb_map_items1
                 sign1 morphism1 symbol1 raw_symbol1 proof_tree1
                 lid2 sublogics2 basic_spec2 sentence2 
                 symb_items2 symb_map_items2
                 sign2 morphism2 symbol2 raw_symbol2 proof_tree2 =>
  GMorphism cid sign1 morphism2 
   -- OmDoc: cid is logic morphism, morphism2 is CASL signature morphism
   -- in the first place, ignore cid and sign1


data Grothendieck = Grothendieck deriving Show


------------------------------------------------------------------
-- Provers
------------------------------------------------------------------

-- | provers and consistency checkers for specific logics
data G_prover = forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_prover lid (Prover sign sentence proof_tree symbol)
     | forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
       G_cons_checker lid (ConsChecker sign sentence morphism proof_tree)


------------------------------------------------------------------
-- Grothendieck diagrams and weakly amalgamable cocones
------------------------------------------------------------------

type GDiagram = Diagram G_sign GMorphism


{-| 
   
Module      :  $Header$

   Central data structure for development graphs.
   Follows Sect. IV:4.2 of the CASL Reference Manual.
-}


-- * Types for structured specification analysis

-- ??? Some info about the theorems already proved for a node
--     should be added
--      or should it be kept separately?
-- what about open theorems of a node???
type NODE_NAME = (SIMPLE_ID, String, Int)

data DGNodeLab = DGNode {
                dgn_name :: NODE_NAME,  -- OmDoc: ID / Name
                dgn_sign :: G_sign,     -- OmDoc: cd / list of symbols
                dgn_sens :: G_l_sentence_list, -- OmDoc: axioms 
                                -- (or simple definition, see axiom name part "def")
                         -- perhaps introduce additional field, 
                         -- correspondning to OmDocs definitions
                -- OmDoc assertions: create new field dgn_theorems ::  G_l_sentence_list
                dgn_nf :: Maybe Node,   -- OmDoc: ???
                dgn_sigma :: Maybe GMorphism,   -- OmDoc: ???
                dgn_origin :: DGOrigin   -- OmDoc: ???
              }
            | DGRef {
                dgn_renamed :: NODE_NAME,  -- OmDoc: ID / Name
                dgn_libname :: LIB_NAME,   -- OmDoc: URI
                dgn_node :: Node,          -- OmDoc: ID / Name
		dgn_nf :: Maybe Node,   -- OmDoc: ???
		dgn_sigma :: Maybe GMorphism   -- OmDoc: ???
              } deriving (Show,Eq) 

           
data DGLinkLab = DGLink {
              -- dgl_name :: String,
              -- dgl_src, dgl_tar :: DGNodeLab,  -- already in graph structure
              dgl_morphism :: GMorphism,   -- OmDoc: Morphism. Logic translation?
              dgl_type :: DGLinkType,
              dgl_origin :: DGOrigin }
              deriving (Eq,Show)


data ThmLinkStatus =  Open | Proven [DGLinkLab] deriving (Eq, Show) -- OmDoc: proof object

data DGLinkType = LocalDef -- OmDoc: imports element of theory, attribute local
            | GlobalDef -- OmDoc: imports element of theory, attribute global
            | HidingDef -- OmDoc: ???
            | FreeDef NodeSig -- the "parameter" node -- OmDoc: ???
            | CofreeDef NodeSig -- the "parameter" node -- OmDoc: ???
	    | LocalThm ThmLinkStatus Conservativity ThmLinkStatus  -- OmDoc: axiom inclusion
               -- ??? Some more proof information is needed here
               -- (proof tree, ...)
	    | GlobalThm ThmLinkStatus Conservativity ThmLinkStatus -- OmDoc: theory inclusion
	    | HidingThm GMorphism ThmLinkStatus -- OmDoc: ???
            | FreeThm GMorphism Bool -- OmDoc: ???
              -- DGLink S1 S2 m2 (DGLinkType m1 p) n
              -- corresponds to a span of morphisms
              -- S1 <--m1-- S --m2--> S2
              deriving (Eq,Show)

data Conservativity = None | Cons | Mono | Def
              deriving (Eq,Ord)
    -- OmDoc: Def corresponds to OmDoc implicit definition
    -- inductive definition: only after analysis
    -- OmDoc has nothing for Cons, Mono
    -- None can be ignored

data DGOrigin = DGBasic | DGExtension | DGTranslation | DGUnion | DGHiding 
              | DGRevealing | DGRevealTranslation | DGFree | DGCofree 
              | DGLocal | DGClosed | DGClosedLenv | DGLogicQual | DGLogicQualLenv 
              | DGData
              | DGFormalParams | DGImports | DGSpecInst SIMPLE_ID | DGFitSpec 
              | DGView SIMPLE_ID | DGFitView SIMPLE_ID | DGFitViewImp SIMPLE_ID
              | DGFitViewA SIMPLE_ID | DGFitViewAImp SIMPLE_ID | DGProof
              deriving (Eq,Show)

type DGraph = Graph DGNodeLab DGLinkLab

data NodeSig = NodeSig (Node,G_sign) | EmptyNode AnyLogic
               deriving (Eq,Show)


data ExtNodeSig = ExtNodeSig (Node,G_ext_sign) | ExtEmptyNode AnyLogic
               deriving (Eq,Show)


-- import, formal parameters, united signature of formal params, body
type ExtGenSig = (NodeSig,[NodeSig],G_sign,NodeSig)

-- source, morphism, parameterized target
type ExtViewSig = (NodeSig,GMorphism,ExtGenSig)


-- * Types for architectural and unit specification analysis
-- (as defined for basic static semantics in Chap. III:5.1)

type ParUnitSig = ([NodeSig], NodeSig)

data UnitSig = Unit_sig NodeSig
	     | Par_unit_sig ParUnitSig 
	       deriving (Show, Eq)

type ImpUnitSig = (NodeSig, UnitSig)
data ImpUnitSigOrSig = Imp_unit_sig ImpUnitSig 
		     | Sig NodeSig
		       deriving (Show, Eq)

type StUnitCtx = Map.Map SIMPLE_ID ImpUnitSigOrSig

type ArchSig = (StUnitCtx, UnitSig)


-- * Types for global and library environments

data GlobalEntry = SpecEntry ExtGenSig 
                 | ViewEntry ExtViewSig
                 | ArchEntry ArchSig
                 | UnitEntry UnitSig 
                 | RefEntry deriving (Show,Eq)

type GlobalEnv = Map.Map SIMPLE_ID GlobalEntry

type GlobalContext = (GlobalAnnos,GlobalEnv,DGraph)

type LibEnv = Map.Map LIB_NAME GlobalContext

