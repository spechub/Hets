
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

emptyState :: AnnoState
emptyState = AnnoState [] []

initAnnos :: AParser ()
initAnnos = setState emptyState

addAnnos :: AParser ()
addAnnos = 
    do AnnoState oldL as <- getState 
       l <- mLineAnnos
       a <- skip >> annotations
       setState $ AnnoState (oldL ++ as ++ l) a 

getLineAnnos :: AParser [Annotation]
getLineAnnos = do AnnoState l as <- getState 
		  setState $ AnnoState [] as
		  return l
getAnnos :: AParser [Annotation]
getAnnos = do AnnoState l as <- getState 
	      initAnnos 
	      return (l ++ as)

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
