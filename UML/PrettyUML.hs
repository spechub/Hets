module UML.PrettyUML where
import UML.UML
import qualified Data.Map as Map
import Common.Doc
import Common.DocUtils
import Common.Keywords

instance Pretty Model where
	pretty (ClassModel cm) = pretty cm

instance Pretty CM where 
	pretty cm = sep $ map pretty (Map.elems $ cmClasses cm)

instance Pretty Class where
	pretty cl = (((text.className) cl) ) <> (parens $ foldl (<>) empty $ punctuate comma (map (text.showClassEntityName) (super cl)))
		<+> ( sep $ map pretty  $ attr cl)
		<+> ( sep $ map pretty  $ proc cl)

instance Pretty Attribute where 
	pretty at = ((text.attrName) at) <> colon <> ((pretty.attrType) at) <>  lbrack <> ((text.attrLowerValue) at) <> comma <+> ((text.attrUpperValue) at) <> rbrack

instance Pretty Procedure where	
	pretty at = ((text.procName) at) <> parens (cat $ map pretty (procPara at)) <> colon <> ((pretty.procReturnType) at)

instance Pretty UMLType where
	pretty (CE en) =  (text.showClassEntityName) en 
	pretty t = (text.show) t

instance Pretty Type where 
	pretty t = (pretty.umltype) t
