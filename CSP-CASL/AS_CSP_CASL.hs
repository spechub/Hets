{- 
  File:           HetCATS/CSP-CASL/AS_CSP_CASL.hs
  Authors:        Daniel Pratsch
  last modified:  24.11.2002

   This is the Abstract Syntax tree of CSP-CASL CSP_CASL_SPEC
-}

module AS_CSP_CASL where

import AS_Basic_CASL
import Id


data CSP_CASL_C_SPEC = Csp_casl_c_spec DATA_DEFN CHANNEL_DECL PROCESS_DEFN
		   deriving (Show,Eq)


type DATA_DEFN = BASIC_SPEC -- will become a structured spec later


data CHANNEL_DECL = Channel_items [CHANNEL_ITEM]
		   deriving (Show,Eq)

data CHANNEL_ITEM = Channel_decl [CHANNEL_NAME] SORT
		   deriving (Show,Eq)

type CHANNEL_NAME = SIMPLE_ID


type PROCESS_NAME = SIMPLE_ID

data EVENT        = Term TERM
                  | Send CHANNEL_NAME TERM 
                  | Receive CHANNEL_NAME VAR SORT
		   deriving (Show,Eq)

data PROCESS_DEFN = Basic PROCESS
		   deriving (Show,Eq)

data PROCESS      =  Named_process PROCESS_NAME
                  |  Generic_named_process PROCESS_NAME TERM
                  |  Skip
                  |  Stop
                  |  Prefix EVENT PROCESS
{-
                  | multiple_prefix VAR EVENT-SET PROCESS
-}
                  | Sequential [PROCESS]

                  | External_choice [PROCESS]
                  | Internal_choice [PROCESS]
{-
                  | alphabet_parallel PROCESS EVENT-SET PROCESS
                  | general_parallel PROCESS EVENT-SET EVENT-SET PROCESS
                  | synchronous_parallel PROCESS+
                  | interleaving_parallel PROCESS+
                  | hiding PROCESS EVENT-SET
                  | renaming PROCESS CSP-RENAMING
                  | conditional FORMULA PROCESS PROCESS
                  | channel_parallel PROCESS CHANNEL-NAME CHANNEL-NAME PROCESS
-}
		   deriving (Show,Eq)








{-
data CHANNEL_DECL = Channel_items CHANNEL_ITEMS
		   deriving (Show,Eq)

data CHANNEL_ITEMS = Channel_item [CHANNEL_ITEM]
		   deriving (Show,Eq)

-- type CHANNEL_NAME = SIMPLE_ID
data CHANNEL_NAME = Simple_id
		   deriving (Show,Eq)


data PROCESS = Skip
		   deriving (Show,Eq)

-}


{-


data SIG_ITEMS = Sort_items [Annoted SORT_ITEM] [Pos] 
	         -- pos: sort, semi colons
	       | Op_items [Annoted OP_ITEM] [Pos]
		 -- pos: op, semi colons
	       | Pred_items [Annoted PRED_ITEM] [Pos]
		 -- pos: pred, semi colons
	       | Datatype_items [Annoted DATATYPE_DECL] [Pos]
		 -- type, semi colons
		 deriving (Show,Eq)

data SORT_ITEM = Sort_decl [SORT] [Pos]
	         -- pos: commas
	       | Subsort_decl [SORT] SORT [Pos]
		 -- pos: commas, <
	       | Subsort_defn SORT VAR SORT (Annoted FORMULA) [Pos]
		 -- pos: "=", "{", ":", ".", "}"
	       | Iso_decl [SORT] [Pos]
	         -- pos: "="s
		 deriving (Show,Eq)

data OP_ITEM = Op_decl [OP_NAME] OP_TYPE [OP_ATTR] [Pos]
	       -- pos: commas, colon, OP_ATTR sep. by commas
	     | Op_defn OP_NAME OP_HEAD (Annoted TERM) [Pos]
	       -- pos: "="
	       deriving (Show,Eq)

data OP_TYPE = Total_op_type [SORT] SORT [Pos]
	       -- pos: "*"s, "->" ; if null [SORT] then [Pos] = [] 
	     | Partial_op_type [SORT] SORT [Pos]
	       -- pos: "*"s, "->?"; if null [SORT] then pos: "?"
	       deriving (Show,Eq)

data OP_HEAD = Total_op_head [ARG_DECL] SORT [Pos]
	       -- pos: "(", semicolons, ")", colon
	     | Partial_op_head [ARG_DECL] SORT [Pos]
	       deriving (Show,Eq)

data ARG_DECL = Arg_decl [VAR] SORT [Pos]
	        -- pos: commas, colon
		deriving (Show,Eq)

data OP_ATTR = Assoc_op_attr | Comm_op_attr | Idem_op_attr
	     | Unit_op_attr TERM
	       deriving (Show,Eq)

data PRED_ITEM = Pred_decl [PRED_NAME] PRED_TYPE [Pos]
                 -- pos: commas, colon
	       | Pred_defn PRED_NAME PRED_HEAD (Annoted FORMULA) [Pos]
		 -- pos: "<=>"
		 deriving (Show,Eq)

data PRED_TYPE = Pred_type [SORT] [Pos]
	         -- pos: if null [SORT] then "(",")" else "*"s
		 deriving (Show,Eq)

data PRED_HEAD = Pred_head [ARG_DECL] [Pos]
	         -- pos: "(",semi colons , ")"
		 deriving (Show,Eq)

data DATATYPE_DECL = Datatype_decl SORT [Annoted ALTERNATIVE] [Pos] 
		     -- pos: "::=", "|"s
		     deriving (Show,Eq)

data ALTERNATIVE = Total_construct OP_NAME [COMPONENTS] [Pos]
		   -- pos: "(", semi colons, ")"
		 | Partial_construct OP_NAME [COMPONENTS] [Pos]
		   -- pos: "(", semi colons, ")", "?"
		 | Subsorts [SORT] [Pos]
		   -- pos: sort, commas
		   deriving (Show,Eq)

data COMPONENTS = Total_select [OP_NAME] SORT [Pos]
                  -- pos: commas, colon
		| Partial_select [OP_NAME] SORT [Pos] 
		  -- pos: commas, ":?"
		| Sort SORT		  
		  deriving (Show,Eq)

data VAR_DECL = Var_decl [VAR] SORT [Pos]
	        -- pos: commas, colon
		deriving (Show,Eq)

{- Position definition for FORMULA: 
   Information on parens are also encoded in [Pos].  If there
   are more Pos than necessary there is a pair of Pos enclosing the
   other Pos informations which encode the brackets of every kind
-}

data FORMULA = Quantification QUANTIFIER [VAR_DECL] FORMULA [Pos]
	       -- pos: QUANTIFIER, semi colons, dot
	     | Conjunction [FORMULA] [Pos]
	       -- pos: "/\"s
	     | Disjunction [FORMULA] [Pos]
	       -- pos: "\/"s
	     | Implication FORMULA FORMULA [Pos]
	       -- pos: "=>" or "if" 	   
	     | Equivalence FORMULA FORMULA [Pos]
	       -- pos: "<=>"
	     | Negation FORMULA [Pos]
	       -- pos: not
	     | True_atom [Pos]
	       -- pos: true	    
	     | False_atom [Pos]
               -- pos: false
	     | Predication PRED_SYMB [TERM] [Pos]
               -- pos: opt. "(",commas,")"
	     | Definedness TERM [Pos]
	       -- pos: def
	     | Existl_equation TERM TERM [Pos]
               -- pos: =e=
	     | Strong_equation TERM TERM [Pos]
	       -- pos: =
	     | Membership TERM SORT [Pos]
               -- pos: in
	     | Mixfix_formula TERM  -- Mixfix_ Term/Token/(..)/[..]/{..}
	     -- a formula left original for mixfix analysis
	     | Unparsed_formula String [Pos]
	       -- pos: first Char in String
	       deriving (Show,Eq)

data QUANTIFIER = Universal | Existential | Unique_existential
		  deriving (Show,Eq)

data PRED_SYMB = Pred_name PRED_NAME 
	       | Qual_pred_name PRED_NAME PRED_TYPE [Pos]
		 -- pos: "(", pred, colon, ")"
		 deriving (Show,Eq)

data TERM = Simple_id SIMPLE_ID    -- "Var" might be a better constructor
	  | Qual_var VAR SORT [Pos]
	    -- pos: "(", var, colon, ")"
	  | Application OP_SYMB [TERM] [Pos]
	    -- pos: parens around [TERM] if any and seperating commas
	  | Sorted_term TERM SORT [Pos]
	    -- pos: colon
	  | Cast TERM SORT [Pos]
	    -- pos: "as"
	  | Conditional TERM FORMULA TERM [Pos]
	    -- pos: "when", "else"
	  | Unparsed_term String [Pos]        -- SML-CATS

	  -- A new intermediate state
          | Mixfix_qual_pred PRED_SYMB -- as part of a mixfix formula
          | Mixfix_term  [TERM]  -- not starting with Mixfix_sorted_term/cast
	  | Mixfix_token Token   -- NO-BRACKET-TOKEN, LITERAL, PLACE
	  | Mixfix_sorted_term SORT [Pos]
	    -- pos: colon
	  | Mixfix_cast SORT [Pos]
	    -- pos: "as" 
          | Mixfix_parenthesized [TERM] [Pos]  -- non-emtpy term list
	    -- pos: "(", commas, ")" 
          | Mixfix_bracketed [TERM] [Pos]
	    -- pos: "[", commas, "]" 
          | Mixfix_braced [TERM] [Pos]         -- also for list-notation 
	    -- pos: "{", "}" 
	    deriving (Show,Eq)

data OP_SYMB = Op_name OP_NAME
	     | Qual_op_name OP_NAME OP_TYPE [Pos]
		 -- pos: "(", op, colon, ")"
	       deriving (Show,Eq)

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
{-* Generated by DrIFT-v1.2 : Look, but Don't Touch. *-}

instance PosItem BASIC_ITEMS where
    up_pos_l _ (Sig_items aa) = (Sig_items aa)
    up_pos_l fn1 (Free_datatype aa ab) = (Free_datatype aa (fn1 ab))
    up_pos_l fn1 (Sort_gen aa ab) = (Sort_gen aa (fn1 ab))
    up_pos_l fn1 (Var_items aa ab) = (Var_items aa (fn1 ab))
    up_pos_l fn1 (Local_var_axioms aa ab ac) =
	(Local_var_axioms aa ab (fn1 ac))
    up_pos_l fn1 (Axiom_items aa ab) = (Axiom_items aa (fn1 ab))
    get_pos_l (Sig_items _) = Nothing
    get_pos_l (Free_datatype _ ab) = Just ab
    get_pos_l (Sort_gen _ ab) = Just ab
    get_pos_l (Var_items _ ab) = Just ab
    get_pos_l (Local_var_axioms _ _ ac) = Just ac
    get_pos_l (Axiom_items _ ab) = Just ab

instance PosItem SIG_ITEMS where
    up_pos_l fn1 (Sort_items aa ab) = (Sort_items aa (fn1 ab))
    up_pos_l fn1 (Op_items aa ab) = (Op_items aa (fn1 ab))
    up_pos_l fn1 (Pred_items aa ab) = (Pred_items aa (fn1 ab))
    up_pos_l fn1 (Datatype_items aa ab) = (Datatype_items aa (fn1 ab))
    get_pos_l (Sort_items _ ab) = Just ab
    get_pos_l (Op_items _ ab) = Just ab
    get_pos_l (Pred_items _ ab) = Just ab
    get_pos_l (Datatype_items _ ab) = Just ab

instance PosItem SORT_ITEM where
    up_pos_l fn1 (Sort_decl aa ab) = (Sort_decl aa (fn1 ab))
    up_pos_l fn1 (Subsort_decl aa ab ac) =
	(Subsort_decl aa ab (fn1 ac))
    up_pos_l fn1 (Subsort_defn aa ab ac ad ae) =
	(Subsort_defn aa ab ac ad (fn1 ae))
    up_pos_l fn1 (Iso_decl aa ab) = (Iso_decl aa (fn1 ab))
    get_pos_l (Sort_decl _ ab) = Just ab
    get_pos_l (Subsort_decl _ _ ac) = Just ac
    get_pos_l (Subsort_defn _ _ _ _ ae) = Just ae
    get_pos_l (Iso_decl _ ab) = Just ab

instance PosItem OP_ITEM where
    up_pos_l fn1 (Op_decl aa ab ac ad) = (Op_decl aa ab ac (fn1 ad))
    up_pos_l fn1 (Op_defn aa ab ac ad) = (Op_defn aa ab ac (fn1 ad))
    get_pos_l (Op_decl _ _ _ ad) = Just ad
    get_pos_l (Op_defn _ _ _ ad) = Just ad

instance PosItem OP_TYPE where
    up_pos_l fn1 (Total_op_type aa ab ac) =
	(Total_op_type aa ab (fn1 ac))
    up_pos_l fn1 (Partial_op_type aa ab ac) =
	(Partial_op_type aa ab (fn1 ac))
    get_pos_l (Total_op_type _ _ ac) = Just ac
    get_pos_l (Partial_op_type _ _ ac) = Just ac

instance PosItem OP_HEAD where
    up_pos_l fn1 (Total_op_head aa ab ac) =
	(Total_op_head aa ab (fn1 ac))
    up_pos_l fn1 (Partial_op_head aa ab ac) =
	(Partial_op_head aa ab (fn1 ac))
    get_pos_l (Total_op_head _ _ ac) = Just ac
    get_pos_l (Partial_op_head _ _ ac) = Just ac

instance PosItem ARG_DECL where
    up_pos_l fn1 (Arg_decl aa ab ac) = (Arg_decl aa ab (fn1 ac))
    get_pos_l (Arg_decl _ _ ac) = Just ac


instance PosItem PRED_ITEM where
    up_pos_l fn1 (Pred_decl aa ab ac) = (Pred_decl aa ab (fn1 ac))
    up_pos_l fn1 (Pred_defn aa ab ac ad) =
	(Pred_defn aa ab ac (fn1 ad))
    get_pos_l (Pred_decl _ _ ac) = Just ac
    get_pos_l (Pred_defn _ _ _ ad) = Just ad

instance PosItem PRED_TYPE where
    up_pos_l fn1 (Pred_type aa ab) = (Pred_type aa (fn1 ab))
    get_pos_l (Pred_type _ ab) = Just ab

instance PosItem PRED_HEAD where
    up_pos_l fn1 (Pred_head aa ab) = (Pred_head aa (fn1 ab))
    get_pos_l (Pred_head _ ab) = Just ab

instance PosItem DATATYPE_DECL where
    up_pos_l fn1 (Datatype_decl aa ab ac) =
	(Datatype_decl aa ab (fn1 ac))
    get_pos_l (Datatype_decl _ _ ac) = Just ac

instance PosItem ALTERNATIVE where
    up_pos_l fn1 (Total_construct aa ab ac) =
	(Total_construct aa ab (fn1 ac))
    up_pos_l fn1 (Partial_construct aa ab ac) =
	(Partial_construct aa ab (fn1 ac))
    up_pos_l fn1 (Subsorts aa ab) = (Subsorts aa (fn1 ab))
    get_pos_l (Total_construct _ _ ac) = Just ac
    get_pos_l (Partial_construct _ _ ac) = Just ac
    get_pos_l (Subsorts _ ab) = Just ab

instance PosItem COMPONENTS where
    up_pos_l fn1 (Total_select aa ab ac) =
	(Total_select aa ab (fn1 ac))
    up_pos_l fn1 (Partial_select aa ab ac) =
	(Partial_select aa ab (fn1 ac))
    up_pos_l _ (Sort aa) = (Sort aa)
    get_pos_l (Total_select _ _ ac) = Just ac
    get_pos_l (Partial_select _ _ ac) = Just ac
    get_pos_l (Sort _) = Nothing

instance PosItem VAR_DECL where
    up_pos_l fn1 (Var_decl aa ab ac) = (Var_decl aa ab (fn1 ac))
    get_pos_l (Var_decl _ _ ac) = Just ac

instance PosItem FORMULA where
    up_pos_l fn1 (Quantification aa ab ac ad) =
	(Quantification aa ab ac (fn1 ad))
    up_pos_l fn1 (Conjunction aa ab) = (Conjunction aa (fn1 ab))
    up_pos_l fn1 (Disjunction aa ab) = (Disjunction aa (fn1 ab))
    up_pos_l fn1 (Implication aa ab ac) = (Implication aa ab (fn1 ac))
    up_pos_l fn1 (Equivalence aa ab ac) = (Equivalence aa ab (fn1 ac))
    up_pos_l fn1 (Negation aa ab) = (Negation aa (fn1 ab))
    up_pos_l fn1 (True_atom aa) = (True_atom (fn1 aa))
    up_pos_l fn1 (False_atom aa) = (False_atom (fn1 aa))
    up_pos_l fn1 (Predication aa ab ac) = (Predication aa ab (fn1 ac))
    up_pos_l fn1 (Definedness aa ab) = (Definedness aa (fn1 ab))
    up_pos_l fn1 (Existl_equation aa ab ac) =
	(Existl_equation aa ab (fn1 ac))
    up_pos_l fn1 (Strong_equation aa ab ac) =
	(Strong_equation aa ab (fn1 ac))
    up_pos_l fn1 (Membership aa ab ac) = (Membership aa ab (fn1 ac))
    up_pos_l _ (Mixfix_formula aa) = (Mixfix_formula aa)
    up_pos_l fn1 (Unparsed_formula aa ab) =
	(Unparsed_formula aa (fn1 ab))
    get_pos_l (Quantification _ _ _ ad) = Just ad
    get_pos_l (Conjunction _ ab) = Just ab
    get_pos_l (Disjunction _ ab) = Just ab
    get_pos_l (Implication _ _ ac) = Just ac
    get_pos_l (Equivalence _ _ ac) = Just ac
    get_pos_l (Negation _ ab) = Just ab
    get_pos_l (True_atom aa) = Just aa
    get_pos_l (False_atom aa) = Just aa
    get_pos_l (Predication _ _ ac) = Just ac
    get_pos_l (Definedness _ ab) = Just ab
    get_pos_l (Existl_equation _ _ ac) = Just ac
    get_pos_l (Strong_equation _ _ ac) = Just ac
    get_pos_l (Membership _ _ ac) = Just ac
    get_pos_l (Mixfix_formula _) = Nothing
    get_pos_l (Unparsed_formula _ ab) = Just ab


instance PosItem PRED_SYMB where
    up_pos_l _ (Pred_name aa) = (Pred_name aa)
    up_pos_l fn1 (Qual_pred_name aa ab ac) =
	(Qual_pred_name aa ab (fn1 ac))
    get_pos_l (Pred_name _) = Nothing
    get_pos_l (Qual_pred_name _ _ ac) = Just ac

instance PosItem TERM where
    up_pos_l _ (Simple_id aa) = (Simple_id aa)
    up_pos_l fn1 (Qual_var aa ab ac) = (Qual_var aa ab (fn1 ac))
    up_pos_l fn1 (Application aa ab ac) = (Application aa ab (fn1 ac))
    up_pos_l fn1 (Sorted_term aa ab ac) = (Sorted_term aa ab (fn1 ac))
    up_pos_l fn1 (Cast aa ab ac) = (Cast aa ab (fn1 ac))
    up_pos_l fn1 (Conditional aa ab ac ad) =
	(Conditional aa ab ac (fn1 ad))
    up_pos_l fn1 (Unparsed_term aa ab) = (Unparsed_term aa (fn1 ab))
    up_pos_l _ (Mixfix_qual_pred aa) = (Mixfix_qual_pred aa)
    up_pos_l _ (Mixfix_term aa) = (Mixfix_term aa)
    up_pos_l _ (Mixfix_token aa) = (Mixfix_token aa)
    up_pos_l fn1 (Mixfix_sorted_term aa ab) =
	(Mixfix_sorted_term aa (fn1 ab))
    up_pos_l fn1 (Mixfix_cast aa ab) = (Mixfix_cast aa (fn1 ab))
    up_pos_l fn1 (Mixfix_parenthesized aa ab) =
	(Mixfix_parenthesized aa (fn1 ab))
    up_pos_l fn1 (Mixfix_bracketed aa ab) =
	(Mixfix_bracketed aa (fn1 ab))
    up_pos_l fn1 (Mixfix_braced aa ab) = (Mixfix_braced aa (fn1 ab))
    get_pos_l (Simple_id _) = Nothing
    get_pos_l (Qual_var _ _ ac) = Just ac
    get_pos_l (Application _ _ ac) = Just ac
    get_pos_l (Sorted_term _ _ ac) = Just ac
    get_pos_l (Cast _ _ ac) = Just ac
    get_pos_l (Conditional _ _ _ ad) = Just ad
    get_pos_l (Unparsed_term _ ab) = Just ab
    get_pos_l (Mixfix_qual_pred _) = Nothing
    get_pos_l (Mixfix_term _) = Nothing
    get_pos_l (Mixfix_token _) = Nothing
    get_pos_l (Mixfix_sorted_term _ ab) = Just ab
    get_pos_l (Mixfix_cast _ ab) = Just ab
    get_pos_l (Mixfix_parenthesized _ ab) = Just ab
    get_pos_l (Mixfix_bracketed _ ab) = Just ab
    get_pos_l (Mixfix_braced _ ab) = Just ab

instance PosItem OP_SYMB where
    up_pos_l _ (Op_name aa) = (Op_name aa)
    up_pos_l fn1 (Qual_op_name aa ab ac) =
	(Qual_op_name aa ab (fn1 ac))
    get_pos_l (Op_name _) = Nothing
    get_pos_l (Qual_op_name _ _ ac) = Just ac

instance PosItem SYMB_ITEMS where
    up_pos_l fn1 (Symb_items aa ab ac) = (Symb_items aa ab (fn1 ac))
    get_pos_l (Symb_items _ _ ac) = Just ac

instance PosItem SYMB_ITEMS_LIST where
    up_pos_l fn1 (Symb_items_list aa ab) =
	(Symb_items_list aa (fn1 ab))
    get_pos_l (Symb_items_list _ ab) = Just ab

instance PosItem SYMB_MAP_ITEMS where
    up_pos_l fn1 (Symb_map_items aa ab ac) =
	(Symb_map_items aa ab (fn1 ac))
    get_pos_l (Symb_map_items _ _ ac) = Just ac

instance PosItem SYMB_MAP_ITEMS_LIST where
    up_pos_l fn1 (Symb_map_items_list aa ab) =
	(Symb_map_items_list aa (fn1 ab))
    get_pos_l (Symb_map_items_list _ ab) = Just ab


instance PosItem SYMB where
    up_pos_l _ (Symb_id aa) = (Symb_id aa)
    up_pos_l fn1 (Qual_id aa ab ac) = (Qual_id aa ab (fn1 ac))
    get_pos_l (Symb_id _) = Nothing
    get_pos_l (Qual_id _ _ ac) = Just ac


instance PosItem SYMB_OR_MAP where
    up_pos_l _ (Symb aa) = (Symb aa)
    up_pos_l fn1 (Symb_map aa ab ac) = (Symb_map aa ab (fn1 ac))
    get_pos_l (Symb _) = Nothing
    get_pos_l (Symb_map _ _ ac) = Just ac

--  Imported from other files :-

-}