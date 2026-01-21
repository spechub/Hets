{-# LANGUAGE DeriveDataTypeable #-}
-- |This module implements an institution for UML Class Diagrams as described
-- in the DOL standard - at least the signature and the sentences
module UML.Sign where

--import CommonLogic.Sign
import           Data.List
import           UML.UML
import           UML.UML   ()
import           Common.Id
import           Data.Data(Data,Typeable)

-- |The signature
data Sign = Sign {
    signClassHier    :: ([ClassEntity], [(ClassEntity, ClassEntity)]),
    signAttribute    :: [(Class, String, Type)],
    signOperations   :: [(Class, String, [(String, Type)], Type)],
    signCompositions :: [((String, ClassEntity), String, (String, Type))],
    signAssociations :: [(String, [(String, Type)])]
    } deriving (Eq, Ord, Show)

-- | checks whether an Signature is empty
emptySign :: Sign
emptySign = Sign {
    signClassHier = ([], []),
    signAttribute = [],
    signOperations = [],
    signCompositions = [],
    signAssociations = []
    }

-- | The multiplicity formulas as defined by the specified grammar (see DOL)
data Sen = NLeqF NumLit FunExpr 
                | FLeqN FunExpr NumLit deriving (Eq, Ord, Show, Typeable, Data)
data FunExpr = NumComp MFCOMPOSITION MFEnd 
                | NumAss MFASSOCIATION MFEnd 
                | NumAttr MFATTRIBUTE deriving (Eq, Ord, Show, Typeable, Data)
data MFATTRIBUTE = MFAttribute MFClassifier MFEnd MFTYPE deriving (Eq, Ord, Show, Typeable, Data)
data MFCOMPOSITION = MFComposition MFName MFEnd MFTYPE MFEnd MFTYPE deriving (Eq, Ord, Show, Typeable, Data)
data MFASSOCIATION = MFAssociation MFName [(MFEnd, MFTYPE)] deriving (Eq, Ord, Show, Typeable, Data)
type MFClassifier = MFName
type MFEnd = MFName
data MFTYPE = MFType Annot MFClassifier deriving (Eq, Ord, Show, Typeable, Data)
type NumLit = Integer
data Annot = OrderedSet | Set | Sequence | Bag deriving (Eq, Ord, Show, Typeable, Data)
type MFName = String

instance GetRange Sen where
  getRange _ = nullRange
  rangeSpan _ = []



comp2mfcomp :: ((String, ClassEntity), String, (String, Type)) -> MFCOMPOSITION
comp2mfcomp ((on, ce), n, (tn, tart)) = MFComposition n on (MFType Set $ showClassEntityName ce) tn (type2mftype tart)

-- |Converts a UMLType to a \tau expressions from DOL
type2mftype :: Type -> MFTYPE
type2mftype t = case (typeOrdered t, typeUnique t) of
                    (True, True) -> MFType OrderedSet (umlTypeString $ umltype t)
                    (True, False) -> MFType Sequence (umlTypeString $ umltype t)
                    (False, True) -> MFType Set (umlTypeString $ umltype t)
                    (False, False) -> MFType Bag (umlTypeString $ umltype t)

-- |Constructs the multiplicity expression for a given association
asso2mfasso :: (String, [(String, Type)]) -> MFASSOCIATION
asso2mfasso (n, lis) = MFAssociation n (map end2mfend lis)

-- |Returns the end expression and type of a given association end
end2mfend :: (String, Type) -> (MFEnd, MFTYPE)
end2mfend (n, t) = (n, type2mftype t)

annotString :: Annot -> String
annotString = show

-- |Constructs the multiplicity expression for a given attribute
attr2mfattr :: (Class, String, Type) -> MFATTRIBUTE
attr2mfattr (cs, s, t) = MFAttribute (className cs) s (type2mftype t)


