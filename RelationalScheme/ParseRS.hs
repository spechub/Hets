{- |
Module      :  $Header$
Description :  abstract syntax for Relational Schemes
Copyright   :  Dominik Luecke, Uni Bremen 2008
License     :  similar to LGPL, see Hets/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for Relational Schemes
-}

module RelationalScheme.ParseRS where

import Common.AnnoState
import Common.Id
import Common.Lexer
import Common.AS_Annotation
import Control.Monad
import RelationalScheme.Keywords
import RelationalScheme.Sign
import RelationalScheme.AS
import qualified Data.Set as Set
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error

foldRanges :: [Token] -> Range
foldRanges inR = foldl (\x y -> appRange x $ tokPos y) nullRange inR

-- ^ parse a simple word not in 'rskeywords'
rsVarId :: [String] -> AParser st Token
rsVarId ks =
     do
        tk <- pToken (reserved (ks++rsKeyWords) (scanAnyWords))
        addAnnos
        return tk

-- ^ Token parser that does not skip whitespaces
pTokenN :: CharParser st String -> CharParser st Token
pTokenN parser =
  bind (\ p s -> Token s (Range [p])) getPos (parser)

-- ^ parser for simple ids
rsSimpleId :: GenParser Char st Token
rsSimpleId = pTokenN (reserved rsKeyWords scanAnyWords)

parseRSScheme :: AParser st RSScheme
parseRSScheme =
    do
        spaces
        pos1 <- getPos
        tb <- parseRSTables
        rl <- parseRSRelationships
        pos2 <- getPos
        return $ RSScheme tb rl $ Range [pos1,pos2]
        
-- ^ Parser for set of relationships
parseRSRelationships :: AParser st RSRelationships
parseRSRelationships =
    do
        k <- asKey rsRelationships
        r <- many parseRSRel
        return $ RSRelationships r $ catPos [k]

-- ^ Parser for a single relationship
parseRSRel :: AParser st (Annoted RSRel)
parseRSRel =
    do
        la <- getAnnos
        l <- sepBy1 parseRSQualId commaT
        k <- asKey rsArrow
        r <- sepBy1 parseRSQualId commaT
        c <- parseRSRelTypes
        ra <- getAnnos
        return $ makeAnnoted la ra (RSRel l r c $ tokPos k)

-- ^ Parser for qualified Ids... 
parseRSQualId :: AParser st RSQualId
parseRSQualId =
    do
        tn <- rsSimpleId
        string "."
        cn <- rsVarId []
        return $ RSQualId (simpleIdToId tn) (simpleIdToId cn) $ foldRanges [tn,cn]
        

-- ^ parser for collection of tables
parseRSTables :: AParser st RSTables
parseRSTables =
    do
        k <- asKey rsTables
        t <- many parseRSTable
        return $ RSTables 
                    {
                        tables = Set.fromList t
                    ,   rst_pos = tokPos k
                    }
        
-- ^ parser for table
parseRSTable :: AParser st RSTable
parseRSTable = 
    do
        la <- getAnnos
        tid <- rsVarId []
        oParenT
        cl <- sepBy1 parseRSColumn commaT
        cParenT
        ra <- getAnnos
        return $ RSTable 
            {
                t_name  = simpleIdToId tid
            ,   columns = setDatatype cl
            ,   t_pos   = tokPos tid
            ,   rsannos = la ++ ra
            ,   t_keys  = Set.fromList $ map c_name $ filter (\x -> c_key x == True) cl
            }

parseRSColumn :: AParser st RSColumn
parseRSColumn = 
    do
        iid <- rsVarId []
        dt <- check4Datatype
        iK <- look4Key
        return $ RSColumn (simpleIdToId iid) dt iK $ foldRanges [iid]

setDatatype :: [RSColumn] -> [RSColumn]
setDatatype inL = reverse $ setDatatypeHelper (reverse inL)

setDatatypeHelper :: [RSColumn] -> [RSColumn]
setDatatypeHelper inL = case inL of
    [] -> []
    (x:xs) -> let 
                tmp_type = c_data x
                (p,r)    = span (\y -> c_data y == RSLikeNext) xs
                op = map (\y -> y {
                                    c_data = tmp_type
                                  }) p
              in 
                (x:op)++setDatatypeHelper r


check4Datatype :: AParser st RSDatatype
check4Datatype =
    do
        try $ colonT
        dt <- parseRSDatatypes
        return $ dt
   <|>
        return RSLikeNext

look4Key :: AParser st Bool
look4Key = 
    do 
        asKey rsKey
        return True
    <|>
        return False

testParse ::GenParser tok (AnnoState ()) a
            -> [tok]
            -> Either Text.ParserCombinators.Parsec.Error.ParseError a
testParse par st = runParser par (emptyAnnos ()) "" st

longTest :: IO (Either ParseError RSScheme)
longTest = do x <- (readFile "RelationalScheme/test/rel.het"); return $ testParse parseRSScheme x

-- boring parser for rel types
parseRSRelTypes :: AParser st RSRelType
parseRSRelTypes =
    do
        asKey rs1to1
        return $ RSone_to_one
    <|>
    do
        asKey rs1tom
        return $ RSone_to_many
    <|>
    do
        asKey rsmto1
        return $ RSmany_to_one
     <|>
    do
        asKey rsmtom
        return $ RSmany_to_many
        
-- boring parser for data-types
parseRSDatatypes :: AParser st RSDatatype
parseRSDatatypes = 
    do
        asKey rsBool
        return $ RSboolean
    <|>
    do
        asKey rsBin
        return $ RSbinary
    <|>
    do
        asKey rsDate
        return $ RSdate
     <|>
    do
        asKey rsDatetime
        return $ RSdatetime      
     <|>
    do
        asKey rsDecimal
        return $ RSdecimal        
     <|>
    do
        asKey rsFloat
        return $ RSfloat      
      <|>
    do
        asKey rsInteger
        return $ RSinteger
     <|>
    do
        asKey rsString
        return $ RSstring    
     <|>
    do
        asKey rsText
        return $ RStext
     <|>
    do
        asKey rsTime
        return $ RStime
      <|>
    do
        asKey rsTimestamp
        return $ RStimestamp
        
makeAnnoted :: [Annotation] -> [Annotation] -> a -> Annoted a
makeAnnoted l r sen = Annoted
                          {
                            item = sen
                          , l_annos = l
                          , r_annos = r
                          , opt_pos = nullRange
                          }
                          
        