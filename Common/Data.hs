{- |
Module      :  ./Common/Data.hs
Description :  generate output from Data instances
Copyright   :  (c) Christian Maeder, DFKI GmbH 2014
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

preprocess some known data types
-}

module Common.Data where

import Common.Id
import Common.IRI
import Common.Result

import Data.Data
import Data.List

data MyData = Builtin String String -- label and content
  | ListOrTuple Bool [MyData] -- True means list
  | Cons String (Maybe [String]) [MyData] -- with optional field names
  deriving (Show, Eq, Ord)

{- | conversion with special treatment for numbers, booleans, strings,
characters, ranges, ids, IRIs and other lists. -}
dataToMyData :: Data a => a -> MyData
dataToMyData a = let
    l = gmapQ dataToMyData a
    c = toConstr a
    fs = constrFields c
    s = showConstr c
    bool = const $ Builtin "bool" s :: Bool -> MyData
    res = case l of
      [] -> case s of
        "[]" -> ListOrTuple True []
        "()" -> ListOrTuple False []
        _ -> Cons s Nothing []
      [hd, ListOrTuple True rt] | s == "(:)" -> ListOrTuple True $ hd : rt
      _ | isPrefixOf "(," s -> ListOrTuple False l
      _ -> Cons s
        (if length fs == length l && all (not . null) fs
         then Just fs else Nothing) l
  in case dataTypeRep $ dataTypeOf a of
  r | elem r [IntRep, FloatRep] -> Builtin "number" s
  CharRep -> Builtin "char" s
  _ -> maybe
       (maybe
        (maybe
         (maybe
          (maybe res
           (Builtin "iri" . iriToStringUnsecure) $ cast a)
          (Builtin "id" . (`showId` "")) $ cast a)
         (Builtin "range" . show . prettyRange . rangeToList) $ cast a)
       (Builtin "string") $ cast a) bool $ cast a

normalizeMyDataForSerialization :: MyData -> MyData
normalizeMyDataForSerialization = stripDeleted . stripSpecialConstructors
  where
    {- "_deleted" is not a valid Haskell constructor and can't clash with real
    data. It is used for marking a deleted data item. -}
    deletedData :: MyData
    deletedData = Cons "_deleted" Nothing []

    isNotDeleted :: MyData -> Bool
    isNotDeleted d = d /= deletedData

    stripSpecialConstructors :: MyData -> MyData
    stripSpecialConstructors md = case md of
      Cons "Nothing" Nothing [] -> deletedData
      Cons "Just" Nothing [value] -> value
      Cons "Left" Nothing [value] -> value
      Cons "Right" Nothing [value] -> value
      Cons constructor fieldsM values ->
        Cons constructor fieldsM $ map stripSpecialConstructors values
      ListOrTuple isList values ->
        ListOrTuple isList $ map stripSpecialConstructors values
      _ -> md

    stripDeletedList :: [MyData] -> [MyData]
    stripDeletedList values = filter isNotDeleted $ map stripDeleted values

    stripDeletedFieldsList :: [String] -> [MyData] -> ([String], [MyData])
    stripDeletedFieldsList fields values =
      unzip $
      filter (\ (_, v) -> isNotDeleted v) $
      map (\ (f, v) -> (f, stripDeleted v)) $
      zip fields values

    stripDeleted :: MyData -> MyData
    stripDeleted md = case md of
      ListOrTuple isList values ->
        ListOrTuple isList $ stripDeletedList values
      Cons constructor Nothing values ->
        Cons constructor Nothing $ stripDeletedList values
      Cons constructor (Just fields) values ->
        let (fields', values') = stripDeletedFieldsList fields values
        in Cons constructor (Just fields') values'
      _ -> md
