{- |
Module      :  $Header$
Copyright   :  (c) Francisc-Nicolae Bungiu
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

RDF constructs

References:
 <http://www.informatik.uni-bremen.de/~till/papers/ontotrans.pdf>
-}

module RDF.AS where

import Common.Id
import RDF.Keywords

import Data.Char (intToDigit)
import Data.List
import Data.Maybe
import qualified Data.Map as Map

data Signature = Sign [ResourceReference]

data Sentence = Sen (Subject Predicate Object)

data RDFTriple = Triple (Subject Object Predicate)

data Subject = URIref | BlankNode
data Predicate = URIref
data Object = URIref | Literal | BlankNode

data Node = URIref | Literal | BlankNode deriving (Show, Eq, Ord)

data Datatype = ValueSpace | LexicalSpace | Map.Map ValueSpace LexicalSpace

data TypedOrUntyped = Typed Datatype | Untyped (Maybe LanguageTag)
    deriving (Show, Eq, Ord)

data Literal = Literal LexicalForm TypedOrUntyped 
    deriving (Show, Eq, Ord)
