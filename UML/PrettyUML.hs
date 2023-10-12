module UML.PrettyUML where

import           Common.Doc      hiding (Label)
import           Common.DocUtils
import qualified Data.Map        as Map
import           Data.Maybe
import           UML.Sign
import           UML.UML

instance Pretty Model where
    pretty (ClassModel cm) = pretty cm
    pretty _ = error "unimplemented"

instance Pretty CM where
    pretty cm = (sep $ map pretty (Map.elems $ cmClasses cm))
                $+$ (vcat $ map pretty (Map.elems $ cmAssociations cm))
                $+$ (vcat $ map pretty (cmPackages cm))

instance Pretty Class where
    pretty cl = (((text . className) cl) ) <> (parens $ foldl (<>) empty $ punctuate comma (map (text . showClassEntityName) (super cl)))
        <+> ( sep $ map pretty  $ attr cl)
        <+> ( sep $ map pretty  $ proc cl)

instance Pretty Attribute where
    pretty at = ((text . attrName) at) <> colon <> ((pretty . attrType) at) <>  lbrack <> ((text . attrLowerValue) at) <> comma <+> ((text . attrUpperValue) at) <> rbrack

instance Pretty Procedure where
    pretty at = ((text . procName) at) <> parens (cat $ map pretty (procPara at)) <> colon <> ((pretty . procReturnType) at)

instance Pretty Association where
    pretty ass = case isComposition ass of
                    False -> (text $ assoName ass)
                                <+> (brackets $ sep $ punctuate comma $ map pretty $ ends ass)
                    True -> (text $ assoName ass) <> text "[Composition]" <> colon <+> (pretty $ head $ ends ass) <+>  text "<>--" <+> (pretty $ head $ tail $ ends ass)
instance Pretty Package where
    pretty pack = (sep $ map pretty (Map.elems $ classes pack))
                $+$ (vcat $ map pretty (Map.elems $ associations pack))
                $+$ (vcat $ map pretty (packagePackages pack))

instance Pretty End where
    pretty end =  ((text . (fromMaybe "") . endName) end) <> colon <> (text $ showClassEntityName $ endTarget end) <>  lbrack <> ((text . lowerValue . label) end) <> comma <+> ((text . upperValue . label) end) <> rbrack

instance Pretty UMLType where
    pretty (CE en) =  (text . showClassEntityName) en
    pretty t = (text . show) t

instance Pretty Type where
    pretty t = (pretty . umltype) t

instance Pretty UML.Sign.Sen where
    pretty (NLeqF n f) = pretty $ (show n) ++ "<=" ++ (show f)
    pretty (FLeqN f n) = pretty $ (show f) ++ "<=" ++ (show n)
instance Pretty Sign where
    pretty _ = pretty $ ""
