
{- HetCATS/CASL/AnnoState.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   a state to collect annotations
-}

module Common.AnnoState where

import Common.Lexer
import Common.AS_Annotation
import Common.Anno_Parser
import Common.Lib.Parsec

-- ----------------------------------------------
-- annotations
-- ----------------------------------------------
type AParser a = GenParser Char AnnoState a

aParse :: AParser a -> GenParser Char st a
aParse p = parseWithState p emptyAnnos

data AnnoState = AnnoState { toAnnos :: [Annotation] }

emptyAnnos :: AnnoState
emptyAnnos = AnnoState []

parseAnnos :: AnnoState -> GenParser Char st AnnoState 
parseAnnos (AnnoState as) = 
    do a <- skip >> annotations
       return $ AnnoState (as ++ a) 

parseLineAnnos :: AnnoState -> GenParser Char st AnnoState 
parseLineAnnos (AnnoState as) = 
    do l <- mLineAnnos
       return $ AnnoState (as ++ l) 

addAnnos :: AParser ()
addAnnos = getState >>= parseAnnos >>= setState

addLineAnnos :: AParser ()
addLineAnnos = getState >>= parseLineAnnos >>= setState

getAnnos :: AParser [Annotation]
getAnnos = do AnnoState a <- getState 
	      setState emptyAnnos 
	      return a

-- annotations on one line
mLineAnnos :: GenParser Char st [Annotation]
mLineAnnos = 
    do p <- getPosition
       do a <- annotationL
	  skipSmart
	  do  l <- mLineAnnos
	      return (a:l)
            <|> return [a]
	 <|> return []
