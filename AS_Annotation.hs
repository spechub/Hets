module AS_Annotation where
import Id

data Annotation = Comment_line String 
		| Comment_group [String]
		-- constructors for unparsed annotes
		| Annote_line(String,String)
		| Annote_group(String,[String])
		-- known annotes
		| Display_anno(Id, [(String,String)])
		| String_anno(Id,Id)
		| List_anno(Id,Id,Id)
		| Number_anno(Id)
		| Float_anno(Id,Id)
		| Prec_anno(Bool,[Id],[Id]) -- true = < , false = <>
		| Lassoc_anno [Id]
		| Rassoc_anno [Id]
		| Label [String]
		| Implies | Definitional | Conservative
		-- position information for annotations 
		| Pos_anno(Region,Annotation)
		  deriving (Show,Eq)   
