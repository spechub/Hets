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
		-- postion of comment start, keywords and comment end
		| String_anno Id Id [Pos] 
		-- postion of comment start, commas and comment end
		| List_anno Id Id Id [Pos] 
		-- postion of comment start, commas and comment end
		| Number_anno Id [Pos] 
		-- postion of comment start, commas and comment end
		| Float_anno Id Id [Pos] 
		-- postion of comment start, commas and comment end
		| Prec_anno Bool [Id] [Id] [Pos] 
		--          ^              ^ p{:[p,]++[p}]++[p<]++
		--          |                 [p{]++[p,]++[p}]
		--          | true = <   false = <>
		| Lassoc_anno [Id] [Pos] -- position of commas
		| Rassoc_anno [Id] [Pos] -- position of commas
		| Label [String] [Pos] 
		-- postion of comment start and comment end

		-- All annotations below are only as commentline allowed
		| Logic_anno  String String [Pos] 
		-- position of comment start, first string, snd string
		| Hide_anno  String String String [Pos] 
		-- position of comment start, 1st str, 2nd str, 3rd str
		| With_anno  String String String [Pos]
		-- position of comment start, 1st str, 2nd str, 3rd str
		| Implies | Definitional | Conservative
		-- position information for annotations is now provided 
		-- by every annotation
		-- | Pos_anno Region Annotation 
		  deriving (Show,Eq)   


data Annoted a = Annoted { item::a
			 , opt_pos::[Pos]
			 , annos::[Annotation]}
		 deriving (Show,Eq) 