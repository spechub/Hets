
{- HetCATS/AS_Annotation.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   These datastructures describe the Annotaions of (Het)CASL. 
   There is also a type class for Annoted items.

   todo:
      - ATermConversion SML-CATS
      - LaTeX Pretty Printing
-}

module AS_Annotation where
import Id

{-! global: ATermConvertible !-}

data Annotation = Comment_line String [Pos]
		| Comment_group [String] [Pos]
		-- constructors for unparsed annotes
		| Annote_line String String [Pos]
		| Annote_group String [String] [Pos]
		-- known annotes
		| Display_anno Id [(String,String)] [Pos]
		-- postion of anno start, keywords and anno end
		| String_anno Id Id [Pos] 
		-- postion of anno start, commas and anno end
		| List_anno Id Id Id [Pos] 
		-- postion of anno start, commas and anno end
		| Number_anno Id [Pos] 
		-- postion of anno start, commas and anno end
		| Float_anno Id Id [Pos] 
		-- postion of anno start, commas and anno end
		| Prec_anno Bool [Id] [Id] [Pos] 
		--          ^              ^ "{",commas,"}", "<",
		--          |                "{",commas,"}"
		--          | true = <   false = <>
		| Lassoc_anno [Id] [Pos] -- position of commas
		| Rassoc_anno [Id] [Pos] -- position of commas
		| Label [String] [Pos] 
		-- postion of anno start and anno end

		-- All annotations below are only as annotationline allowed
		| Implies [Pos] 
		| Definitional [Pos]
		| Conservative [Pos]
		-- position information for annotations is now provided 
		-- by every annotation
		-- | Pos_anno Region Annotation 
		  deriving (Show,Eq)   


data Annoted a = Annoted { item::a
			 , opt_pos::[Pos]
			 , l_annos, r_annos::[Annotation]}
	                   -- left or preceeding, right or following
		 deriving (Show,Eq) 