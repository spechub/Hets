{-# OPTIONS -fglasgow-exts -fth -cpp #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Serializer.Datatypes
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
--
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A Generic XML Serializer using HXT and the Generics package (SYB3). This new version of
-- GXS is based on type classes, and thus allows modular customization. More coming soon.
--
-- This is the set of data-types (and non-dependant classes) which are used during the serialization
-- process. This is very much a work in process. We also provide the functions required for monadic
-- deserialization via ReadX. It's a lot simpler than it was in the old GXS. We also supply particle
-- reader for the various parts of an XML document.
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the
-- GNU General Public License as published by the Free Software Foundation; either version 2
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not,
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Text.XML.Serializer.Datatypes where

import Data.Generics2
import Text.XML.HXT.Parser
import Text.XML.HXT.DOM.QualifiedName
import Data.DynamicMap
import Network.URI
import Control.Monad.State hiding (lift)
import Data.List
import Data.Maybe
import Data.Char
import Data.Dynamic
import Data.Array hiding (inRange)
import Language.Haskell.TH.Syntax

-- | SerializeTree is a tree with leaves, nodes and index branches, which convey information (mostly about Choice blocks)
type SerializePart a = [(SerializeNode a, a)]
type SerializeTree a = [SerializeNode a]
data SerializeNode a = SLeaf a | SNode [SerializeTree a] | SIndex Int (SerializeTree a)

-- | Flatten a serialize node to a single XmlFilter
flattenSNode :: SerializeNode XmlFilter -> XmlFilter
flattenSNode (SLeaf x)     = x
flattenSNode (SNode tss)   = cat $ map flattenSNode $ concat tss
flattenSNode (SIndex i ts) = cat $ map flattenSNode ts

-- | Flatten a deserialize node to a single XmlTrees
flattenDNode :: SerializeNode (XmlTrees, XmlTrees) -> XmlTrees
flattenDNode (SLeaf (x,_)) = x
flattenDNode (SNode tss)   = concat $ map flattenDNode $ concat tss
flattenDNode (SIndex i ts) = concat $ map flattenDNode ts

instance Show (SerializeNode XmlFilter) where
    show (SLeaf f) = "Leaf(" ++ (xmlTreesToString $ f emptyRoot) ++ ")"
    show (SNode l) = "Node : " ++ show l
    show (SIndex i t) = "I:" ++ show i ++ ":" ++ show t

instance Show (SerializeNode (XmlTrees, XmlTrees)) where
    show (SLeaf (e,a)) = "Leaf(" ++ (xmlTreesToString e) ++ ":" ++ xmlTreesToString a ++ ")"
    show (SNode l) = "Node : " ++ show l
    show (SIndex i t) = "I:" ++ show i ++ ":" ++ show t


-- | Attach a filter to a serialize node
appendFilter :: XmlFilter -> SerializeNode XmlFilter -> SerializeNode XmlFilter
appendFilter f t = case t of SLeaf  x   -> SLeaf (x+++f)
                             SNode  x   -> SNode (x++[[SLeaf f]])
                             SIndex i x -> SIndex i (x++[SLeaf f])

-- | Attach an attribute to a serialize tree
addAttribute :: [XmlFilter] -> SerializeTree XmlFilter -> SerializeTree XmlFilter
addAttribute as ts = zipWith (\a t -> case t of
                                          SLeaf x -> SLeaf (x +++ a)
                                          e       -> e) as ts

type LowerBound = Int
-- | Data-type for the upper bounds of cardinality
data UpperBound = Bounded Int | Unbounded

instance Show UpperBound where
    show x = case x of Bounded n -> show n
                       Unbounded -> "unbounded"

-- | Concrete data-type for particle cardinality.
data Occurs = Occurs { occurs_min :: LowerBound,
                       occurs_max :: UpperBound }

mkOccurs :: Cardinality a => a -> Occurs
mkOccurs x = Occurs (minOccurs x) (maxOccurs x)

instance Show Occurs where
    show c = "(" ++ show (occurs_min c) ++ " <-> " ++ show (occurs_max c) ++ ")"

-- Various constructions functions for Occurs
occursOnce  = Occurs 1 (Bounded 1)
occursMaybe = Occurs 0 (Bounded 1)
occursAny   = Occurs 0 Unbounded
occursN l u = Occurs l (Bounded u)
(<->) = occursN

-- | Any entity which has cardinality should instantiate this class
class Cardinality a where
    getCardinality :: a -> (LowerBound, UpperBound)
    minOccurs      :: a -> LowerBound
    minOccurs = fst . getCardinality
    maxOccurs      :: a -> UpperBound
    maxOccurs = snd . getCardinality

-- | Whether a given cardinal entity's range includes the given value.
inRange :: Cardinality a => Int -> a -> Bool
inRange n c = ((n >= minOccurs c)&&(case maxOccurs c of Unbounded -> True
                                                        Bounded x -> n <= x))

instance Cardinality Occurs where
    getCardinality (Occurs min max) = (min, max)

{- Each data-type should eventually allow these encodings to be stored per field, so that we can finally
   abandon the nasty field-name hack (e_, a_, s_). Eventually algebraic data-types should allow us to use
   a list of these things to perform serialization (i.e. serialize each sub-term and then use these to wrap them
   up appropriately).
-}

-- Although Attributes can't have a full range of cardinality, we might as well represent it.

-- FIXME: Ok, we've got a problem here. If we represent an Attribute as a particle, it means that when reading a sequence it will
-- try to read each attribute over and over. What we really want is to restrict attributes to complex types and remove them from here,
-- however that would mean that you couldn't just have a list of these to describe how a field should be serialized.

-- | Representation of XML particles
data PartSchema =  Attr Occurs  String (Maybe URI) | -- ^ Attribute Descriptor, treat uniformly with elements as much as possible
                   Elem Occurs  String (Maybe URI) | -- ^ Element Descriptor
                   Choice Occurs   [PartSchema]    | -- ^ Choice Descriptor
                   Sequence Occurs [PartSchema]    | -- ^ Sequence Descriptor
                   Inter Occurs    [PartSchema]    | -- ^ Interleaving, more expressive than XML-S <all/>
                   AnyAttr AnyRes                  | -- ^ Attribute wildcard
                   AnyElement Occurs AnyRes        | -- ^ Element Wild-Card
                   ChildDefault                    | -- ^ Use the default name data on the child data to serialize
                   TextContent                       -- ^ Plain XText Content
                   deriving Show

#ifndef __HADDOCK__
instance (Lift i, Lift e, Ix i) => Lift (Array i e) where
    lift a = [| listArray $(lift (bounds a)) $(lift (assocs a)) |]

instance Lift URIAuth where
    lift (URIAuth u r p) = [| URIAuth u r p |]

instance Lift URI where
    lift (URI s a p q f) = [| URI s a p q f |]

#if __GLASGOW_HASKELL__<=604
instance Lift a => Lift (Maybe a) where
    lift (Just x) = [| Just x |]
    lift Nothing  = [| Nothing |]
#endif

instance Lift UpperBound where
    lift (Bounded x) = [| Bounded x |]
    lift Unbounded = [| Unbounded |]

instance Lift Occurs where
    lift (Occurs l u) = [| Occurs l u |]

instance Lift AnyRes where
    lift AnyNS   = [| AnyNS |]
    lift OtherNS  = [| OtherNS |]
    lift (ListNS l) = [| ListNS l |]

instance Lift PartSchema where
    lift (Elem o s u) = [| Elem o s u |]
    lift (Attr o s u) = [| Attr o s u |]
    lift (Choice o s) = [| Choice o s |]
    lift (Sequence o s) = [| Sequence o s |]
    lift (Inter o s) = [| Inter o s |]
    lift (AnyAttr a) = [| AnyAttr a |]
    lift (AnyElement o a) = [| AnyElement o a |]
#endif

-- | Set the cardinality for any XML particle schema.
setSchemaOccurs :: Occurs -> PartSchema -> PartSchema
setSchemaOccurs c s = case s of
                             Attr _ n ns    -> Attr c n ns
                             Elem _ n ns    -> Elem c n ns
                             Choice _ p     -> Choice c p
                             Sequence _ p   -> Sequence c p
                             Inter _ p      -> Inter c p
                             AnyElement _ p -> AnyElement c p

-- | Restrictions on a wild-card particle.
data AnyRes  = AnyNS | OtherNS | ListNS [URI] deriving Show

-- | A set of attributes.
data AttrSet = AttrSet [(QName, String)] deriving Show

-- | A set of elements.
data ElemSet = ElemSet [(QName, String)] deriving Show

lookupAttrSet :: (String, String) -> AttrSet -> Maybe String
lookupAttrSet (n, ns) (AttrSet l) = (liftM snd) $ find (\x -> let (QN _ l q) = fst x in (l==n && ns==q)) l

-- | Wrap up a serialize tree using the given particle schema. Takes namespace table, scope, part-schema and serialize tree.
xmlWrap :: [(URI, String)] -> Maybe URI -> PartSchema -> SerializeTree XmlFilter -> XmlFilter
xmlWrap nst scope f t = if (null t) then none else -- FIXME: This is a hack, does it allow named, but empty particles? I think it should...
    case f of
        Attr c n ns -> let q = nameToQName n ns' nst; ns' = if (ns==scope) then Nothing else ns in
                               qattr q $ txt $ concat $ intersperse " " $ map (\x -> xmlTreesToString $ flattenSNode x $ emptyRoot) t
        Elem c n ns -> let q = nameToQName n ns nst in
                                 cat $ map (\x -> qetag q += flattenSNode x) t
        Choice c fs -> cat $ map (wrapChoice fs) t
        Sequence c fs -> cat $ map (wrapSequence fs) t
        Inter c fs    -> cat $ map (wrapSequence fs) t -- I think that writing an Inter should be pretty much the same as a Sequence
        AnyAttr _     -> cat $ map flattenSNode t
        AnyElement _ _ -> cat $ map flattenSNode t
        TextContent    -> cat $ map flattenSNode t
        ChildDefault   -> xmlWrap nst scope defaultChildDefault t
    where wrapChoice fs t   = case t of
                                  x@(SLeaf f) -> xmlWrap nst scope (head fs) [t] -- Default case, something has probably gone wrong.
                                  x@(SNode _) -> xmlWrap nst scope (head fs) [t]
                                  SIndex i ts -> xmlWrap nst scope (fs!!(i-1)) ts

          wrapSequence fs t = case t of
                                  x@(SLeaf _) -> xmlWrap nst scope (head fs) [t] -- Default case, something has probably gone wrong.
                                  SNode x     -> foldr (+++) none $ zipWith (xmlWrap nst scope) fs x
                                  SIndex i x  -> xmlWrap nst scope f x

defaultChildDefault = Elem (1<->1) "item" Nothing


-- | A descriptor for a data-type, most of the time should provide enough data to serialize.
data XMLType = XMLType { fieldSchema    :: Array Int [PartSchema]  -- ^ Array denotes each constructor in type, list denotes term
                       , choiceIndex    :: Int                     -- ^ The index for the above
                       , isInterleaved  :: Bool                    -- ^ Whether the given data-type is interleaved.
                       , extensions     :: Int                     -- ^ Number of leading types which are extensions
                       , elementNames   :: [String]                -- ^ List of default element names, one for each constructor
--                       , attributeNames :: [String]
                       , forceDefault   :: Bool
                       , defaultSchema  :: Maybe PartSchema        -- ^ The default part schema for this type
                       , setFlags       :: DynamicMap              -- ^ Any flags this type should propogate
                       , defaultValues  :: [Maybe Dynamic]         -- ^ Default values for the terms
                       , xmlMetaData    :: DynamicMap
                       } deriving Show

-- We can only lift XML Types properly which do not contain default values or flags to set.
#ifndef __HADDOCK__
instance Lift XMLType where
    lift (XMLType a b c d e f g h i j) = [| XMLType a b c d e f g emptyDM [] emptyDM |]
#endif

-- FIXME: Default values should mirror the number of constructors.

getDefaultSchema :: XMLType -> Maybe URI -> PartSchema
getDefaultSchema xc ns = fromJust $ (defaultSchema xc) `mplus` subElems `mplus` (return $ defaultChildDefault)
  where subElems =  case (map (\n -> Elem (1<->1) n ns) (elementNames xc)) of
                        []  -> mzero
                        [x] -> return x
                        l   -> return $ Choice (1<->1) l
-- | Given an XML Constructor from a fully instantiated data-type, return a list of part-schemas for the sub terms.
getConsSchema :: XMLType -> [PartSchema]
getConsSchema xc = (fieldSchema xc) ! (choiceIndex xc)

-- | As above, but make a single particle to describe the whole data-type (used for extensions).
getConsPartSchema :: XMLType -> PartSchema
getConsPartSchema xc = let f = if (isInterleaved xc) then Inter (1<->1) else Sequence (1<->1)
                           l = map f $ elems (fieldSchema xc) in
                           if (length l == 1)
                              then head l
                              else Choice (1<->1) l


-- XMLType filters

-- | Decapitalize the first character of the main element of the field schema.
decap :: XMLType -> XMLType
decap x = x { elementNames = map dc (elementNames x)
--            , attributeNames = map dc (attributeNames x)
            , defaultSchema = (\x -> case x of
                                             Just (Elem o n ns) -> Just (Elem o (dc n) ns)
                                             Just (Attr o n ns) -> Just (Attr o (dc n) ns)
                                             x -> x) $ defaultSchema x
            }
  where dc (h:t) = toLower h:t

-- | Capitalize the first character of the main element of the field schema.
cap :: XMLType -> XMLType
cap x = x { elementNames = map dc (elementNames x)
--            , attributeNames = map dc (attributeNames x)
          , defaultSchema = (\x -> case x of
                                     Just (Elem o n ns) -> Just (Elem o (dc n) ns)
                                     Just (Attr o n ns) -> Just (Attr o (dc n) ns)
                                     x -> x) $ defaultSchema x
          }
  where dc (h:t) = toUpper h:t

-- | Capitalize the first character of all the fields in the field schema.
capFields :: XMLType -> XMLType
capFields = mapFields dc
  where
   dc (h:t) = toUpper h:t

-- | Remove underscores from fields
deusFields :: XMLType -> XMLType
deusFields = mapFields dc
  where
   dc (h:t) = if (h=='_') then t else (h:t)

-- | Remove the name of the
removeFieldLeader x = x { elementNames = map rw (elementNames x)
                        , defaultSchema = (\x -> case x of
                                                        Just (Elem o n ns) -> Just (Elem o (rw n) ns)
                                                        Just (Attr o n ns) -> Just (Attr o (rw n) ns)
                                                        x -> x) $ defaultSchema x
                        }
  where rw (h:t) = if (isLower h) then rw t else toLower h:t
        rw ""    = ""

dropWord1 (h:t)
  | (isLower h) = dropWord1 t
  | (isUpper h) = (toLower h):t
dropWord1 [] = []

mapFields :: (String -> String) -> XMLType -> XMLType
mapFields f x = x { fieldSchema = array (fst $ head asc, fst $ last asc) (map dcf asc)
                  }
  where
   asc = assocs (fieldSchema x)
   dcf (i, e) = (i, map up e)
   up x = case x of
              Elem o n ns -> Elem o (f n) ns
              Attr o n ns -> Attr o (f n) ns
              Choice o es -> Choice o (map up es)
              Sequence o es -> Sequence o (map up es)
              Inter o es    -> Inter o (map up es)
              x -> x

-- | Allow functions to be applied to the different part schemas in an XML Type
mutFields :: [[PartSchema -> PartSchema]] -> XMLType -> XMLType
mutFields fs x = let b = bounds (fieldSchema x); i = indices (fieldSchema x); e = elems (fieldSchema x) in
                     x{fieldSchema=array b $ zip i $ zipWith (zipWith ($)) fs e}

-- | Convert to an element (if possible)
xme :: PartSchema -> PartSchema
xme (Attr o s u) = Elem o s u
xme x = x

-- | Convert to an attribute (if possible)
xma :: PartSchema -> PartSchema
xma (Elem o s u) = Attr o s u
xma x = x

-- | Convert to a child default
xmx :: PartSchema -> PartSchema
xmx _ = ChildDefault

-- | Convert to a text content
xmt :: PartSchema -> PartSchema
xmt _ = TextContent

-- Handy synonyms for writing descriptor code, all allow the production of partial functions for PartSchema
-- of type Maybe URI -> PartSchema, so that all can be given the same namespace in a complex particle structure.

-- | Create an attribute with arbitrary occurance
atr      = Attr occursMaybe
-- | Create an element with single occurance
elm      = elmN occursOnce
-- | Create a sequence with single occurance
seqx     = seqN occursOnce
-- | Create a choice with single occurance
choice   = choiceN occursOnce
-- | Create an attribute wildcard
anyAtr   = const . AnyAttr

-- | Create an element with given occurance
elmN    = Elem
-- | Create a sequence with given occurance
seqN    = \c x ns -> Sequence c (map (\f -> f ns) x)
-- | Create a choice with given occurance
choiceN = \c x ns -> Choice c (map (\f -> f ns) x)

-- | Create a complete fields descriptor with given namespace, should be used with above synonyms
-- e.g. fieldsQ [elm "hello", elm "bye", atr "anAttr"] myNamespace
fieldsQ :: [Maybe URI -> PartSchema] -> Maybe URI -> Array Int [PartSchema]
fieldsQ l u = listArray (1,1) [map (\f -> f u) l]

-- | The default values of the XMLType; useful for only changing the stuff you need to.

xmlType = XMLType (listArray (1,1) [[Elem occursAny "item" Nothing]]) 1 False 0 ["item"] False Nothing emptyDM [] emptyDM
-- Dynamic Map keys

-- | Key to represent namespace table in DynamicMap
nstKey     = newDynamicKey "nstKey"     ([]::[(String, URI)])
-- | Key to represent inverted namespace table (namespace -> prefix) in DynamicMap
nstIKey    = newDynamicKey "nstIKey"    ([]::[(URI, String)])
-- | Key to represent namespace scope in DynamicMap.
nsScopeKey = newDynamicKey "nsScopeKey" (Nothing::Maybe URI)
-- | Key to represent target namespace in DynamicMap.
targetNamespaceKey = newDynamicKey "targetNamespaceKey" (Nothing::Maybe URI)

-----------------------------------------------------------------------------------------------------------------------
-- The ReadX Monad
-----------------------------------------------------------------------------------------------------------------------

-- | Kleisli Combinator
(>@>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >@> g =  \x -> f x >>= g

-- | The state of the reader monad contains
data ReadXO =
    RO { thisConstr    :: Constr
       , thisXMLType   :: XMLType
       , fields        :: [(PartSchema, Maybe Dynamic)]
       , particles     :: SerializeTree (XmlTrees, XmlTrees)
       , elements      :: XmlTrees
       , attributes    :: XmlTrees
       , dynMap        :: DynamicMap -- ^ The Dynamic Map
       , defaultValue  :: Maybe Dynamic
       } -- deriving Show

-- | If the current particle register leads with a particle whose constructor index has been chosen then return the index and
-- the particle associated with this index. Otherwise return no index and the particle anyway.
partIndex :: ReadX (Maybe Int, SerializeTree (XmlTrees, XmlTrees))
partIndex = do s <- get
               if (null $ particles s)
                  then return (Nothing, [])
                  else let (h:_) = particles s in case h of SIndex n t -> return (Just n, t)
                                                            _          -> return (Nothing, particles s)

-- | The monad itself
type ReadX a = StateT (ReadXO) Maybe a

-- | Run the monad and drop into Maybe
runReadX :: ReadXO -> ReadX a -> Maybe a
runReadX s m = liftM fst $ runStateT m s

-- | Run the monad and drop into any MonadPlus
newReadX s m = do let x = runReadX s m
                  maybe mzero return x

-- This should be replaced with proper namespace scoping, but will do for now.
maybeNs lp ns = hasLocalPart lp `o` (hasNamespace "" `orElse` hasNamespace ns)

-- | Repeat a MonadPlus until it fails, returning a list of results.
repeatM :: MonadPlus m => m a -> m [a]
repeatM act = do h <- act
                 t <- repeatM act
                 return (h:t)
              `mplus` return []

repeatMn :: MonadPlus m => Int -> m a -> m [a]
repeatMn n act = if (n==0) then return []
                           else do h <- act
                                   t <- repeatMn (n-1) act
                                   return (h:t)
                                `mplus` return []

repeatMb b act = case (maxOccurs b) of
                     Unbounded -> repeatM act
                     Bounded n -> repeatMn n act

checkOccurs :: MonadPlus m => Occurs -> [a] -> m [a]
checkOccurs o l = if (length l `inRange` o) then return l
                                            else mzero

-- FIXME : The following two functions should be made namespace aware.

-- | Get a single unordered element
get1ElemI :: String -> Maybe URI -> ReadX XmlTree
get1ElemI lp ns = do s <- get
                     let x = elements s
                     let out = find (not . null . hasLocalPart lp) x
                     maybe mzero (\y -> do put s{elements=(delete y x)}
                                           return y) out

-- | Get a single sequential element
get1ElemS :: String -> Maybe URI -> ReadX XmlTree
get1ElemS lp ns = do s <- get
                     let x = elements s
                         q = maybe "" show ns
                     if (null x) then mzero
                                 else do let out = listToMaybe $ maybeNs lp q $ head x
                                         maybe mzero (\y -> do put s{elements=(delete y x)}
                                                               return y) out


-- | Parse a Deserialization Tree from an XmlTree.
parseDTree :: PartSchema -> ReadX (SerializeTree (XmlTrees, XmlTrees))
parseDTree f =
    do s <- get
       let ts = elements s; as = attributes s
       case f of
           Attr c n ns    -> readAttribute c n ns
           Elem c n ns    -> readElement c n ns
           Sequence c fs  -> if (null fs) then mzero else readSequence c fs
           Choice c fs    -> if (null fs) then mzero else readChoice c fs
           Inter c fs     -> if (null fs) then mzero else readInter c fs
           AnyAttr r      -> readAnyAttr r
           AnyElement c r -> readAnyContent c r
           TextContent    -> readTextContent
           ChildDefault   -> mzero -- We shouldn't have been able to get here, the deserializer should insert the child data.

-- Readers for various particle types.

readTextContent :: ReadX (SerializeTree (XmlTrees, XmlTrees))
readTextContent = do s <- get
                     let es = elements s
                     if (null es) then mzero
                                  else do put s{elements = tail es}
                                          return [SLeaf ([head es], [])]


readAnyContent :: Occurs -> AnyRes -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readAnyContent o r = do s <- get
                        let es = elements s
                        ts <- case (r,o) of
                                (AnyNS, Occurs _ Unbounded)   -> put s{elements=[]} >> return es
                                (AnyNS, Occurs l (Bounded u)) -> if (length es < l)
                                                                     then mzero
                                                                     else put s{elements = drop u es} >> (return $ take u es)
                        return $ map (\e -> SLeaf ([e], [])) ts -- Was what was False.


readAnyAttr :: AnyRes -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readAnyAttr r = do s <- get
                   let as = case r of
                                AnyNS -> attributes s

                   return [SLeaf ([], as)]


readAttribute :: Occurs -> String -> Maybe URI -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readAttribute c n ns = do let q = maybe "" show ns
                          s <- get
                          return (map getChildren $ maybeNs n q $$ attributes s) >>= checkOccurs c
                                                                                 >>= return . map (SLeaf . flip (,) [])

readElement :: Occurs -> String -> Maybe URI -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readElement c n ns = repeatMb c (get1ElemS n ns) >>= checkOccurs c
                                                 >>= return . map (\t -> SLeaf (getChildren t, getAttrl t))

readChoice  :: Occurs -> [PartSchema] -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readChoice c fs = do ts <- repeatMb c (msum $ zipWith (\p n -> p >>= \x -> return (x, n)) (map parseDTree fs) [1..])
                                                                 >>= checkOccurs c
                     return $ map (\(t,n) -> SIndex n t) ts

readSequence :: Occurs -> [PartSchema] -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readSequence c fs = repeatMb c (liftM SNode $ mapM parseDTree fs) >>= checkOccurs c


{-
   FIXME: Currently we do not preserve the state of an interleaved data-structure. We really ought to, although that could
   potentially mess up reading off a record using interleaving where order is of no consequence (e.g. GoogleSearch uses interleaving
   for its records). Although since the interleaving in XML-S is pretty nutty anyway, it might need some more development.
-}
readInter :: Occurs -> [PartSchema] -> ReadX (SerializeTree (XmlTrees, XmlTrees))
readInter o fs = repeatMb o (liftM SNode $ mapM (\f -> case f of
                                                           Elem o n ns -> readElemI o n ns
                                                           Attr o n ns -> readAttribute o n ns
                                                           x           -> error $ "Can only interleave elements and attributes"
                                                ) fs) >>= checkOccurs o
    where readElemI c n ns = repeatM (get1ElemI n ns) >>= checkOccurs c
                                                      >>= return . map (\t -> SLeaf (getChildren t, getAttrl t))


readText :: ReadX String
readText = do x <- readTexts
              if (null x) then mzero
                          else return $ concat x

readTexts :: ReadX [String]
readTexts = do s <- get
               return $ map (xmlTreesToString . flattenDNode) (particles s)

-- | Get the next field descriptor, along with a possible default value.
nextField :: ReadX (PartSchema, Maybe Dynamic)
nextField = do s <- get
               put s{fields=tail $ fields s}
               return $ head $ fields s


-- | Get the next particle in the serialize tree.
nextParticle :: ReadX (SerializeTree (XmlTrees, XmlTrees))
nextParticle = do s <- get
                  if (null $ particles s)
                     then mzero
                     else case (head $ particles s) of
                               SLeaf _    -> mzero
                               SIndex _ _ -> mzero
                               SNode l    -> if (null l) then mzero
                                                         else do put s{particles=((SNode $ tail l):(tail $ particles s))}
                                                                 return $ head l


-- | A Dictionary for the XMLData class.
data DictXMLData a = DictXMLData { xmlEncodeD   :: DynamicMap -> a -> SerializeTree XmlFilter
                                 , xmlDecodeD   :: ReadX a
                                 , toXMLTypeD   :: a -> XMLType
                                 , xmlNSDict    :: DictXMLNS a
                                 }
-- | A Dictionary for the XMLNamespace class.
data DictXMLNS a = DictXMLNS { namespaceURID  :: a -> Maybe URI    -- ^ The actual namespace of the entity.
                             , containsNamespacesD :: a -> [URI]   -- ^ A list of namespaces encapsulated in non-entity content.
                             , defaultPrefixD :: a -> String       -- ^ The default prefix (e.g. xsd)
                             }

instance XMLNamespace a => Sat (DictXMLNS a) where
    dict = DictXMLNS { namespaceURID  = namespaceURI
                     , containsNamespacesD = containsNamespaces
                     , defaultPrefixD = defaultPrefix }

-- | The XMLNamespace class allows the storage of a namespace URI, child namespaces and default prefix for a data-type.
class XMLNamespace a where
    namespaceURI  :: a -> Maybe URI
    namespaceURI _ = Nothing
    containsNamespaces :: a -> [URI]
    containsNamespaces _ = []
    defaultPrefix :: a -> String
    defaultPrefix _ = ""


-- | Given a name, namespace and namespace table produce a qualfied name.
nameToQName :: String -> Maybe URI -> [(URI, String)] -> QName
nameToQName n ns nst = fromMaybe (QN "" n "") (do q <- ns
                                                  p <- lookup q nst
                                                  return $ QN p n (show q))


-- | Wrap up a serialization in a number of particles.
ltag :: String -> [[XmlFilter]] -> [XmlFilter]
ltag n f = map (\x -> etag n ++= x) f


applyPrefix :: XMLNamespace a => DynamicMap -> a -> String -> String
applyPrefix dm x = let nst = lookupDM_D nstIKey dm; ns = namespaceURI x; p = ns >>= \x -> lookup x nst in
                             \x -> (maybe "" (\p -> p++":") p)++x

swap (x,y) = (y,x)

-- | Insert a forward namespace table into a DynamicMap.
addNamespaces :: [(String, URI)] -> DynamicMap -> DynamicMap
addNamespaces ns dm = let nst = lookupDM_D nstKey dm; nstI = lookupDM_D nstIKey dm in
                          addToDM (nst++ns) nstKey $ addToDM (nstI++map swap ns) nstIKey dm

-- | Convert a list of lists of XmlFilters, with a specified root name to a list of XmlTrees.
toTrees :: String -> SerializeTree XmlFilter -> XmlTrees
toTrees n fs = (cat $ map (\x -> etag n += (flattenSNode x)) fs) emptyRoot

-- | Produce a filter which adds a namespace table to the root of a tree.
namespaceTableFilter :: [(String, URI)] -> [XmlFilter]
namespaceTableFilter = map (\(p, ns)->attr ("xmlns:"++p) (txt $ show ns))
