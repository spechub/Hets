
{- HetCATS/CASL/AnnoState.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   a state to collect annotations
-}

module AnnoState where

import Lexer
import AS_Annotation
import Anno_Parser
import Parsec

-- ----------------------------------------------
-- annotations
-- ----------------------------------------------
type AParser a = GenParser Char AnnoState a

data AnnoState = AnnoState { lastLines :: [Annotation]
			   , nextAnnos :: [Annotation] }

emptyAnnos :: AnnoState
emptyAnnos = AnnoState [] []

parseAnnos :: AnnoState -> GenParser Char st AnnoState 
parseAnnos (AnnoState oldL as) = 
    do l <- mLineAnnos
       a <- skip >> annotations
       return $ AnnoState (oldL ++ as ++ l) a 

addAnnos :: AParser ()
addAnnos = getState >>= parseAnnos >>= setState

splitLineAnnos :: AnnoState -> (AnnoState, [Annotation])
splitLineAnnos (AnnoState l as) = (AnnoState [] as, l)

getLineAnnos :: AParser [Annotation]
getLineAnnos = do a <- getState 
		  let (b , l) = splitLineAnnos a
		  setState b
		  return l

toAnnos :: AnnoState -> [Annotation]
toAnnos (AnnoState l as) = l ++ as

getAnnos :: AParser [Annotation]
getAnnos = do a <- getState 
	      setState emptyAnnos 
	      return $ toAnnos a

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
