{-# OPTIONS -fglasgow-exts #-}
module Simple where

import Text.ParserCombinators.Parsec

data HData a = O | C a deriving (Eq,Ord,Show)

data IN l = IN Int (HData l) deriving (Eq,Ord,Show)
data CH l = CH Char (HData l) deriving (Eq,Ord,Show)

data Sealed p = forall a. Sealed (p a)
type ParseResult = Sealed HData 

embeddedParser types =  do string "end"; spaces; return $ Sealed O
                    <|> do case (head types) of
                             1 -> do aux <- pInt
                                     Sealed rest <- embeddedParser (tail types)
                                     return (Sealed (C (IN aux rest)))
                             2 -> do aux <- pCh
                                     Sealed rest <- embeddedParser (tail types)
                                     return (Sealed (C (CH aux rest)))
                             _ -> error "unallowed type"

pInt :: Parser Int
pInt =  do n <- fmap read $ many1 digit; return $ fromInteger n

pCh :: Parser Char
pCh =  do c <- letter; return $ c

-- data type works
--sample = In (C(IN 0 (C(CH 'a' (In (C(IN 1 (C(CH 'b' (In (C(IN 2 O))))))))))))
--C(IN 0 (C(CH 'a' (C(IN 1 (C(CH 'b' (C(IN 2 O)))))))))

simple = embeddedParser $cycle [1,2]
-- the above result should be produced by
-- res = parseTest simple "0a1b2end"
