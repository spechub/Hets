{- |
Module      :  ./RelationalScheme/ParseRS.hs
Description :  abstract syntax for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for Relational Schemes
-}

module RelationalScheme.ParseRS
        (
            parseRSScheme
        , testParse
        , longTest
        )
        where

import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.Parsec
import Common.GlobalAnnotations (PrefixMap)

import Control.Monad

import RelationalScheme.AS
import RelationalScheme.Keywords
import RelationalScheme.Sign

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error

import qualified Data.Set as Set
import qualified Data.Map as Map

-- ^ parse a simple word not in 'rskeywords'
rsVarId :: [String] -> AParser st Token
rsVarId ks =
     do
        tk <- pToken $ reserved (ks ++ rsKeyWords) scanAnyWords
        addAnnos
        return tk

parseRSScheme :: PrefixMap -> AParser st RSScheme
parseRSScheme _ =
    do
        spaces
        pos1 <- getPos
        tb <- parseRSTables
        rl <- parseRSRelationships
        pos2 <- getPos
        return $ RSScheme tb rl $ Range [pos1, pos2]

-- ^ Parser for set of relationships
parseRSRelationships :: AParser st RSRelationships
parseRSRelationships =
    do
        k <- try $ asKey rsRelationships
        r <- many parseRSRel
        return $ RSRelationships r $ catRange [k]
    <|>
        return (RSRelationships [] nullRange)

-- ^ Parser for a single relationship
parseRSRel :: AParser st (Annoted RSRel)
parseRSRel =
    do
        la <- getAnnos
        l <- parseRSQualId
        k <- asKey rsArrow
        r <- parseRSQualId
        c <- parseRSRelTypes
        ra <- getAnnos
        return $ makeAnnoted la ra (RSRel l r c $ tokPos k)

-- ^ Parser for qualified Ids...
parseRSQualId :: AParser st [RSQualId]
parseRSQualId =
    do
        tn <- rsVarId []
        oBracketT
        cn <- sepBy1 (rsVarId []) commaT
        cBracketT
        let out = map
              (\ x -> RSQualId (simpleIdToId tn) (simpleIdToId x) $ tokPos x)
              cn
        return out

-- ^ parser for collection of tables
parseRSTables :: AParser st RSTables
parseRSTables =
    do
        try $ asKey rsTables
        t <- many parseRSTable
        ot <- setConv t
        return RSTables
                    {
                        tables = ot
                    }
    <|>
        return RSTables
                    {
                        tables = Set.empty
                    }

setCol :: (Monad m) => [RSColumn] -> m (Set.Set RSColumn)
setCol t =
    let
        names = map c_name t
    in
      do
        foldM_ (flip insertUnique) Set.empty names
        return $ foldl (flip Set.insert) Set.empty t

setConv :: (Monad m) => [RSTable] -> m (Set.Set RSTable)
setConv t =
    let
        names = map t_name t
    in
      do
        foldM_ (flip insertUnique) Set.empty names
        return $ foldl (flip Set.insert) Set.empty t

insertUnique :: (Monad m) => Id -> Set.Set Id -> m (Set.Set Id)
insertUnique t s =
    if t `Set.notMember` s then return $ Set.insert t s
    else fail $ "Duplicate definition of " ++ show t

-- ^ parser for table
parseRSTable :: AParser st RSTable
parseRSTable =
    do
        la <- getAnnos
        tid <- rsVarId []
        oParenT
        cl <- sepBy1 parseRSColumn commaT
        let ccl = concat cl
        setCol ccl
        cParenT
        ra <- getAnnos
        return RSTable
            {
                t_name = simpleIdToId tid
            , columns = ccl
            , rsannos = la ++ ra
            , t_keys = Set.fromList
                  $ map (\ x -> (c_name x, c_data x))
                  $ filter c_key ccl
            }

parseEntry :: AParser st (Token, Bool)
parseEntry =
    do
        iK <- look4Key
        iid <- rsVarId []
        return (iid, iK)

parseRSColumn :: AParser st [RSColumn]
parseRSColumn =
    do
        iid <- sepBy1 parseEntry commaT
        colonT
        dt <- parseRSDatatypes
        return $ map (\ (x, y) -> RSColumn (simpleIdToId x) dt y) iid

look4Key :: AParser st Bool
look4Key =
    do
        asKey rsKey
        return True
    <|>
        return False

testParse :: GenParser tok (AnnoState ()) a
            -> [tok]
            -> Either Text.ParserCombinators.Parsec.Error.ParseError a
testParse par = runParser par (emptyAnnos ()) ""

longTest :: IO (Either ParseError RSScheme)
longTest = do
  x <- readFile "RelationalScheme/test/rel.dol"
  return $ testParse (parseRSScheme Map.empty) x

-- boring parser for rel types
parseRSRelTypes :: AParser st RSRelType
parseRSRelTypes =
    do
        asKey rs1to1
        return RSone_to_one
    <|>
    do
        asKey rs1tom
        return RSone_to_many
    <|>
    do
        asKey rsmto1
        return RSmany_to_one
     <|>
    do
        asKey rsmtom
        return RSmany_to_many

-- boring parser for data-types
parseRSDatatypes :: AParser st RSDatatype
parseRSDatatypes =
    do
        asKey rsBool
        return RSboolean
    <|>
    do
        asKey rsBin
        return RSbinary
    <|>
    do
        asKey rsDate
        return RSdate
     <|>
    do
        asKey rsDatetime
        return RSdatetime
     <|>
    do
        asKey rsDecimal
        return RSdecimal
     <|>
    do
        asKey rsFloat
        return RSfloat
      <|>
    do
        asKey rsInteger
        return RSinteger
     <|>
    do
        asKey rsString
        return RSstring
     <|>
    do
        asKey rsText
        return RStext
     <|>
    do
        asKey rsTime
        return RStime
      <|>
    do
        asKey rsTimestamp
        return RStimestamp
      <|>
    do
        asKey rsDouble
        return RSdouble
      <|>
    do
        asKey rsNonPosInteger
        return RSnonPosInteger
       <|>
    do
        asKey rsNonNegInteger
        return RSnonNegInteger
       <|>
    do
        asKey rsLong
        return RSlong
       <|>
    do
      asKey rsPointer
      return RSPointer


makeAnnoted :: [Annotation] -> [Annotation] -> a -> Annoted a
makeAnnoted l r sen = Annoted
                          {
                            item = sen
                          , l_annos = l
                          , r_annos = r
                          , opt_pos = nullRange
                          }
