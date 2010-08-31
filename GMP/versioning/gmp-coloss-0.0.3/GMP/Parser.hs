{- | Module     : $Header$
 -  Description : Implementation of logic formula parser
 -  Copyright   : (c) Georgel Calin & Lutz Schroeder, DFKI Lab Bremen
 -  License     : GPLv2 or higher, see LICENSE.txt
 -  Maintainer  : g.calin@jacobs-university.de
 -  Stability   : provisional
 -  Portability : portable
 -
 -  Provides the implementation of the generic parser for the L formula datatype
 -}

module GMP.Parser where
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic

-- import Debug.Trace

------------------------------------
-- experiment 2 starting here:
------------------------------------

--class (SigFeature a b (c d), SigFeature b c (e f)) => MyFeat a b c d e f where
--  yoyo :: (a (b (c d))) -> (b (c (e f)))
--  pGoOn3 :: (a (b (c d))) -> ModalOperator ->  GenParser Char st (Formula (b (c (e f))))

--instance MyFeat K K K () K () where
--  yoyo sig = K [Mod (K [Mod (K [])])]
--  pGoOn3 sig flag = primFormula (yoyo sig) flag

--instance MyFeat KD KD KD () KD () where
--  yoyo sig = KD [Mod (KD [Mod (KD [])])]
--  pGoOn3 sig flag = primFormula (yoyo sig) flag

--instance MyFeat K KD K () KD () where
--  yoyo sig = KD [Mod (K [Mod (KD [])])]
--  pGoOn3 sig flag = primFormula (yoyo sig) flag

--instance MyFeat KD K KD () K () where
--  yoyo sig = K [Mod (KD [Mod (K [])])]
--  pGoOn3 sig flag = primFormula (yoyo sig) flag

------------------------------------
-- experiment 1 starting here:
------------------------------------

--class SigFeature a b c => ParseMe a b c where
--  pGive :: (a (b c)) -> (b c)
--  pGoOn2 :: (a (b c)) -> ModalOperator ->  GenParser Char st (Formula (b c))

--instance (SigFeature K K (K d), ParseMe K K d) => ParseMe K K (K d) where
--  pGive = genericPGive
--  pGoOn2 = genericPGoOn2

--instance SigFeature K K () => ParseMe K K () where
--  pGive sig = trace ("finishing: " ++ sPretty sig) $ K []
--  pGoOn2 sig flag = trace ("finishing: " ++ sPretty sig) $ return F

--instance (SigFeature KD KD (KD d), ParseMe KD KD d) => ParseMe KD KD (KD d) where
--  pGive = genericPGive
--  pGoOn2 = genericPGoOn2

--instance SigFeature KD KD () => ParseMe KD KD () where
--  pGive sig = trace ("finishing: " ++ sPretty sig) $ KD []
--  pGoOn2 sig flag = trace ("finishing: " ++ sPretty sig) $ return F

--instance (SigFeature KD K (KD d), ParseMe K KD d) => ParseMe KD K (KD d) where
--  pGive = genericPGive
--  pGoOn2 = genericPGoOn2

--instance SigFeature K KD () => ParseMe K KD () where
--  pGive sig = trace ("finishing: " ++ sPretty sig) $ KD []
--  pGoOn2 sig flag = trace ("finishing: " ++ sPretty sig) $ return F

--instance (SigFeature K KD (K d), ParseMe KD K d) => ParseMe K KD (K d) where
--  pGive = genericPGive
--  pGoOn2 = genericPGoOn2

--instance SigFeature KD K () => ParseMe KD K () where
--  pGive sig = trace ("finishing: " ++ sPretty sig) $ K []
--  pGoOn2 sig flag = trace ("finishing: " ++ sPretty sig) $ return F

--genericPGive :: (SigFeature a b (c d), SigFeature b c d, ParseMe a b (c d), ParseMe b c d) => (a (b (c d))) -> (b (c d))
--genericPGive sig = ((sSecondFeat sig) [Mod ((sSecondFeat (sNextSig sig)) [])])

--genericPGoOn2 :: (SigFeature a b (c d), SigFeature b c d, ParseMe a b (c d), ParseMe b c d) => (a (b (c d))) -> ModalOperator ->  GenParser Char st (Formula (b (c d)))
--genericPGoOn2 sig flag = return T
--genericPGoOn2 sig flag = primFormula (pGive sig) flag

-- generic parsing stuff
genericPGoOn :: (SigFeature a b (c d), SigFeature b c d) => (a (b (c d))) -> ModalOperator ->  Parser (Formula (b (c d)))
genericPGoOn sig flag = primFormula (sNextSig sig) flag

-- parser:

-- Normalised negation.
nneg :: Formula (a b) -> Formula (a b)
nneg F = T
nneg T = F
nneg (Neg phi) = phi
nneg phi = Neg phi

-- | Main parser
parser :: (SigFeature a b c) => (a (b c)) -> ModalOperator -> Parser (Formula (a (b c)) )
parser sig flag = implFormula sig flag

-- | Parser which translates all implications in disjunctions & conjunctions
implFormula :: (SigFeature a b c) => (a (b c)) -> ModalOperator -> Parser (Formula (a (b c)) )
implFormula sig flag = do
    f <- orFormula sig flag
    option f (do string "->"
                 spaces
                 i <- implFormula sig flag
                 return $ Or (Neg f) i
          <|> do try(string "<->")
                 spaces
                 i <- implFormula sig flag
                 return $ And (Or (Neg f) i) (Or f (Neg i))
          <|> do string "<-"
                 spaces
                 i <- implFormula sig flag
                 return $ Or f (Neg i)
          <|> do return f
          <?> "GMPParser.implFormula")

-- | Parser for disjunction - used for handling binding order
orFormula :: (SigFeature a b c) => (a (b c)) -> ModalOperator -> Parser (Formula (a (b c)) )
orFormula sig flag = do
    f <- andFormula sig flag
    option f $ do
      string "\\/"
      spaces
      g <- orFormula sig flag
      return $ Or f g
  <?> "GMPParser.orFormula"

-- | Parser for conjunction - used for handling the binding order
andFormula :: (SigFeature a b c) => (a (b c)) -> ModalOperator -> Parser (Formula (a (b c)) )
andFormula sig flag = do
    f <- primFormula sig flag
    option f $ do
      string "/\\"
      spaces
      g <- andFormula sig flag
      return $ And f g
  <?> "GMPParser.andFormula"

{- | Parse a primitive formula: T, F, ~f, <i>f, [i]f, p*, 
 -   where i stands for an index, f for a formula and 
 -   * for a series of digits i.e. and integer -}
primFormula :: (SigFeature a b c) => (a (b c)) -> ModalOperator -> Parser (Formula (a (b c)) )
primFormula sig flag = 
                  do string "T"
                     spaces
                     return T
              <|> do string "F"
                     spaces
                     return F
              <|> do f <- parenFormula sig flag
                     return f
              <|> do string "~"
                     spaces
                     f <- primFormula sig flag
                     return $ nneg f
              <|> do char '<'
                     spaces
                     i <- sParser sig
                     spaces
                     char '>'
                     spaces
		     f <- sepBy1 (pGoOn sig flag) (string (fSeparator sig))
                     -- restrict to the default modal operator
                     case flag of
                       Ang -> return $ Mod (i f)
                       Sqr -> return $ Neg (Mod (i (map nneg f)))
                       _   -> return $ Mod (i f)
              <|> do char '['
                     spaces
                     i <- sParser sig
                     spaces
                     char ']'
                     spaces
		     f <- sepBy1 (pGoOn sig flag) (string (fSeparator sig))
                     -- restrict to the default modal operator
                     case flag of
                       Sqr -> return $ Mod (i f)
                       Ang -> return $ Neg (Mod (i (map nneg f)))
                       _   -> return $ Mod (i f)
              <|> do char 'p'
                     i <- atomIndex
                     return $ (Atom (fromInteger i))
              <?> "GMPParser.primFormula"

-- | Parser for un-parenthesizing a formula
parenFormula :: (SigFeature a b c) => (a (b c)) -> ModalOperator -> Parser (Formula (a (b c)) )
parenFormula sig flag =  
                   do char '('
                      spaces
                      f <- parser sig flag
                      spaces
                      char ')'
                      spaces
                      return f
               <?> "GMPParser.parenFormula"

-- | Parse integer number
natural :: GenParser Char st Integer
natural = fmap read $ many1 digit 

-- | Parse the possible integer index of a variable
atomIndex :: GenParser Char st Integer
atomIndex =  do i <- try natural
                spaces
                return $ i
         <?> "GMPParser.atomIndex"
