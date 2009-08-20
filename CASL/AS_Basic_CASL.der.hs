{- |
Module      :  $Header$
Description :  Abstract syntax of CASL basic specifications
Copyright   :  (c) Klaus Luettich, Christian Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Abstract Syntax of CASL Basic_specs, Symb_items and Symb_map_items.

   Follows Sect. II:2.2 of the CASL Reference Manual.
-}

module CASL.AS_Basic_CASL where

import Common.Id
import Common.AS_Annotation
import qualified Data.Set as Set

-- DrIFT command
{-! global: GetRange !-}

data BASIC_SPEC b s f = Basic_spec [Annoted (BASIC_ITEMS b s f)]
                  deriving Show

data BASIC_ITEMS b s f = Sig_items (SIG_ITEMS s f)
                   -- the Annotation following the keyword is dropped
                   -- but preceding the keyword is now an Annotation allowed
                 | Free_datatype SortsKind [Annoted DATATYPE_DECL] Range
                   -- pos: free, type, semi colons
                 | Sort_gen [Annoted (SIG_ITEMS s f)] Range
                   -- pos: generated, opt. braces
                 | Var_items [VAR_DECL] Range
                   -- pos: var, semi colons
                 | Local_var_axioms [VAR_DECL] [Annoted (FORMULA f)] Range
                   -- pos: forall, semi colons, dots
                 | Axiom_items [Annoted (FORMULA f)] Range
                   -- pos: dots
                 | Ext_BASIC_ITEMS b
                   deriving Show

data SortsKind = NonEmptySorts | PossiblyEmptySorts deriving Show

data SIG_ITEMS s f = Sort_items SortsKind [Annoted (SORT_ITEM f)] Range
                 -- pos: sort, semi colons
               | Op_items [Annoted (OP_ITEM f)] Range
                 -- pos: op, semi colons
               | Pred_items [Annoted (PRED_ITEM f)] Range
                 -- pos: pred, semi colons
               | Datatype_items SortsKind [Annoted DATATYPE_DECL] Range
                 -- type, semi colons
               | Ext_SIG_ITEMS s
                 deriving Show

data SORT_ITEM f = Sort_decl [SORT] Range
                 -- pos: commas
               | Subsort_decl [SORT] SORT Range
                 -- pos: commas, <
               | Subsort_defn SORT VAR SORT (Annoted (FORMULA f)) Range
                 -- pos: "=", "{", ":", ".", "}"
                 -- the left anno list stored in Annoted Formula is
                 -- parsed after the equal sign
               | Iso_decl [SORT] Range
                 -- pos: "="s
                 deriving Show

data OP_ITEM f = Op_decl [OP_NAME] OP_TYPE [OP_ATTR f] Range
               -- pos: commas, colon, OP_ATTR sep. by commas
             | Op_defn OP_NAME OP_HEAD (Annoted (TERM f)) Range
               -- pos: "="
               deriving Show

data OpKind = Total | Partial deriving (Show, Eq, Ord)

data OP_TYPE = Op_type OpKind [SORT] SORT Range
               -- pos: "*"s, "->" ; if null [SORT] then Range = [] or pos: "?"
               deriving (Show, Eq, Ord)

args_OP_TYPE :: OP_TYPE -> [SORT]
args_OP_TYPE (Op_type _ args _ _) = args

res_OP_TYPE :: OP_TYPE -> SORT
res_OP_TYPE (Op_type _ _ res _) = res

data OP_HEAD = Op_head OpKind [ARG_DECL] SORT Range
               -- pos: "(", semicolons, ")", colon
               deriving Show

data ARG_DECL = Arg_decl [VAR] SORT Range
                -- pos: commas, colon
                deriving Show

data OP_ATTR f = Assoc_op_attr | Comm_op_attr | Idem_op_attr
             | Unit_op_attr (TERM f)
               deriving (Show, Eq, Ord)

data PRED_ITEM f = Pred_decl [PRED_NAME] PRED_TYPE Range
                 -- pos: commas, colon
               | Pred_defn PRED_NAME PRED_HEAD (Annoted (FORMULA f)) Range
                 -- pos: "<=>"
                 deriving Show

data PRED_TYPE = Pred_type [SORT] Range
                 -- pos: if null [SORT] then "(",")" else "*"s
                 deriving (Show, Eq, Ord)

data PRED_HEAD = Pred_head [ARG_DECL] Range
                 -- pos: "(",semi colons , ")"
                 deriving Show

data DATATYPE_DECL = Datatype_decl SORT [Annoted ALTERNATIVE] Range
                     -- pos: "::=", "|"s
                     deriving Show

data ALTERNATIVE = Alt_construct OpKind OP_NAME [COMPONENTS] Range
                   -- pos: "(", semi colons, ")" optional "?"
                 | Subsorts [SORT] Range
                   -- pos: sort, commas
                   deriving Show

data COMPONENTS = Cons_select OpKind [OP_NAME] SORT Range
                  -- pos: commas, colon or ":?"
                | Sort SORT
                  deriving Show

data VAR_DECL = Var_decl [VAR] SORT Range
                -- pos: commas, colon
                deriving (Show, Eq, Ord)

varDeclRange :: VAR_DECL -> [Pos]
varDeclRange (Var_decl vs s _) = case vs of
  [] -> []
  v : _ -> joinRanges [tokenRange v, idRange s]

{- Position definition for FORMULA:
   Information on parens are also encoded in Range.  If there
   are more Pos than necessary there is a pair of Pos enclosing the
   other Pos informations which encode the brackets of every kind
-}

data FORMULA f = Quantification QUANTIFIER [VAR_DECL] (FORMULA f) Range
               -- pos: QUANTIFIER, semi colons, dot
             | Conjunction [FORMULA f] Range
               -- pos: "/\"s
             | Disjunction [FORMULA f] Range
               -- pos: "\/"s
             | Implication (FORMULA f) (FORMULA f) Bool Range
               -- pos: "=>" or "if" (True -> "=>")
             | Equivalence (FORMULA f) (FORMULA f) Range
               -- pos: "<=>"
             | Negation (FORMULA f) Range
               -- pos: not
             | True_atom Range
               -- pos: true
             | False_atom Range
               -- pos: false
             | Predication PRED_SYMB [TERM f] Range
               -- pos: opt. "(",commas,")"
             | Definedness (TERM f) Range
               -- pos: def
             | Existl_equation (TERM f) (TERM f) Range
               -- pos: =e=
             | Strong_equation (TERM f) (TERM f) Range
               -- pos: =
             | Membership (TERM f) SORT Range
               -- pos: in
             | Mixfix_formula (TERM f)  -- Mixfix_ Term/Token/(..)/[..]/{..}
             -- a formula left original for mixfix analysis
             | Unparsed_formula String Range
               -- pos: first Char in String
             | Sort_gen_ax [Constraint] Bool -- flag: belongs to a free type?
             | ExtFORMULA f
             -- needed for CASL extensions
               deriving (Show, Eq, Ord)

is_True_atom, is_False_atom :: FORMULA f -> Bool
is_True_atom (True_atom _) = True
is_True_atom _ = False
is_False_atom (False_atom _) = True
is_False_atom _ = False

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
corresponding to the index.  A negative index indicates a sort outside
the constraint (i.e. a "parameter sort"). Note that this representation of
sort generation constraints is efficiently tailored towards both the use in
the proof calculus (Chap. IV:2, p. 282 of the CASL Reference Manual)
and the coding into second order logic (p. 429 of Theoret. Comp. Sci. 286).
-}

data Constraint = Constraint { newSort :: SORT,
                               opSymbs :: [(OP_SYMB,[Int])],
                               origSort :: SORT }
                  deriving (Show, Eq, Ord)

isInjectiveList :: Ord a => [a] -> Bool
isInjectiveList l = Set.size (Set.fromList l) == length l

-- | from a Sort_gex_ax, recover:
-- | a traditional sort generation constraint plus a sort mapping
recover_Sort_gen_ax :: [Constraint] ->
                        ([SORT],[OP_SYMB],[(SORT,SORT)])
recover_Sort_gen_ax constrs =
  if isInjectiveList sorts
     -- no duplicate sorts, i.e. injective sort map? Then we can ignore indices
     then (sorts,map fst (concat (map opSymbs constrs)),[])
     -- otherwise, we have to introduce new sorts for the indices
     -- and afterwards rename them into the sorts they denote
     else (map indSort1 indices,map indOp indOps1,map sortMap indSorts)
  where
  sorts = map newSort constrs
  indices = [0..length sorts-1]
  indSorts = zip indices sorts
  indSort (i,s) = if i<0 then s else indSort1 i
  indSort1 i = origSort $ head (drop i constrs)
  sortMap (i,s) = (indSort1 i,s)
  indOps = zip indices (map opSymbs constrs)
  indOps1 = concat (map (\(i,ops) -> map ((,) i) ops) indOps)
  indOp (res,(Qual_op_name on (Op_type k args1 res1 pos1) pos,args)) =
     Qual_op_name on
         (Op_type k (map indSort (zip args args1))
                        (indSort (res,res1)) pos1) pos
  indOp _ = error
      "CASL/AS_Basic_CASL: Internal error: Unqualified OP_SYMB in Sort_gen_ax"

-- | from a free Sort_gex_ax, recover:
-- | the sorts, each paired with the constructors
-- | fails (i.e. delivers Nothing) if the sort map is not injective
recover_free_Sort_gen_ax :: [Constraint] -> Maybe [(SORT,[OP_SYMB])]
recover_free_Sort_gen_ax constrs =
  if isInjectiveList sorts
     -- no duplicate sorts, i.e. injective sort map?
     then Just $ map getOpProfile constrs
     else Nothing
  where
  sorts = map newSort constrs
  getOpProfile constr = (newSort constr, map fst $ opSymbs constr)

data QUANTIFIER = Universal | Existential | Unique_existential
                  deriving (Show, Eq, Ord)

data PRED_SYMB = Pred_name PRED_NAME
               | Qual_pred_name PRED_NAME PRED_TYPE Range
                 -- pos: "(", pred, colon, ")"
                 deriving (Show, Eq, Ord)

predSymbName :: PRED_SYMB -> PRED_NAME
predSymbName p = case p of
  Pred_name n -> n
  Qual_pred_name n _ _ -> n

data TERM f = Qual_var VAR SORT Range -- pos: "(", var, colon, ")"
          | Application OP_SYMB [TERM f] Range
            -- pos: parens around TERM f if any and seperating commas
          | Sorted_term (TERM f) SORT Range
            -- pos: colon
          | Cast (TERM f) SORT Range
            -- pos: "as"
          | Conditional (TERM f) (FORMULA f) (TERM f) Range
            -- pos: "when", "else"
          | Unparsed_term String Range        -- SML-CATS

          -- A new intermediate state
          | Mixfix_qual_pred PRED_SYMB -- as part of a mixfix formula
          | Mixfix_term [TERM f]  -- not starting with Mixfix_sorted_term/cast
          | Mixfix_token Token   -- NO-BRACKET-TOKEN, LITERAL, PLACE
          | Mixfix_sorted_term SORT Range
            -- pos: colon
          | Mixfix_cast SORT Range
            -- pos: "as"
          | Mixfix_parenthesized [TERM f] Range  -- non-emtpy term list
            -- pos: "(", commas, ")"
          | Mixfix_bracketed [TERM f] Range
            -- pos: "[", commas, "]"
          | Mixfix_braced [TERM f] Range         -- also for list-notation
            -- pos: "{", "}"
            deriving (Show, Eq, Ord)

-- | state after mixfix- but before overload resolution
varOrConst :: Token -> TERM f
varOrConst t = Application (Op_name $ simpleIdToId t) [] $ tokPos t

data OP_SYMB = Op_name OP_NAME
             | Qual_op_name OP_NAME OP_TYPE Range
                 -- pos: "(", op, colon, ")"
               deriving (Show, Eq, Ord)

opSymbName :: OP_SYMB -> OP_NAME
opSymbName o = case o of
  Op_name n -> n
  Qual_op_name n _ _ -> n

type CASLFORMULA = FORMULA ()
type CASLTERM = TERM ()

type OP_NAME = Id
type PRED_NAME = Id
type SORT = Id
type VAR = Token

data SYMB_ITEMS = Symb_items SYMB_KIND [SYMB] Range
                  -- pos: SYMB_KIND, commas
                  deriving (Show, Eq)

data SYMB_MAP_ITEMS = Symb_map_items SYMB_KIND [SYMB_OR_MAP] Range
                      -- pos: SYMB_KIND, commas
                      deriving (Show, Eq)

data SYMB_KIND = Implicit | Sorts_kind
               | Ops_kind | Preds_kind | OtherKinds String
                 deriving (Show, Eq, Ord)

data SYMB = Symb_id Id
          | Qual_id Id TYPE Range
            -- pos: colon
            deriving (Show, Eq)

data TYPE = O_type OP_TYPE
          | P_type PRED_TYPE
          | A_type SORT -- ambiguous pred or (constant total) op
            deriving (Show, Eq)

data SYMB_OR_MAP = Symb SYMB
                 | Symb_map SYMB SYMB Range
                   -- pos: "|->"
                   deriving (Show, Eq)
