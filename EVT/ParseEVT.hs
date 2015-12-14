module EVT.ParseEVT
        (
	evtBasicSpec
	, parseEVTGuards
	, parseEVTActions
	, parseGuard
	, parseAction
	)
        where

import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Lexer
import Text.ParserCombinators.Parsec
import Common.Keywords
import Common.AnnoState
import Common.GlobalAnnotations (PrefixMap)
import Common.Token (parseId, sortId, varId)

import CASL.AS_Basic_CASL
import qualified CASL.Formula as CASL

import Control.Monad
import Control.Applicative hiding (many)

import EVT.AS 
import EVT.Keywords
import EVT.Sign
import CASL.Parse_AS_Basic
import CASL.OpItem
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error

import qualified Data.Set as Set
import qualified Data.Map as Map

evtBasicSpec :: PrefixMap -> AParser st EVENT
evtBasicSpec _ = do spaces
    	            pos1 <- getPos
		    gs <- many parseEVTGuards
		    as <- many parseEVTActions
	     	    pos2 <- getPos
		    return (EVENT (stringToId "FIXMEINPARSEEVT") gs as) 

parseEVTGuards ::AParser st GUARD
parseEVTGuards=
	do
	   try $ asKey grd
	   gs <- parseGuard   
	   return gs

evtSortId :: AParser st SORT
evtSortId = sortId evtKeywords

parseGuard :: AParser st GUARD
parseGuard= do 
	      gid<-evtSortId
	      spaces
	      pr<-CASL.formula ["Hello", "World"]
	      return GUARD 
	       {
		 gnum = gid
		 , predicate = pr
	       }

parseEVTActions :: AParser st ACTION
parseEVTActions=
	do
	   try $ asKey action
	   as <- parseAction   
	   return as

parseAction :: AParser st ACTION
parseAction =  do 
	      aid<-evtSortId
	      spaces
	      st<-CASL.formula ["Hello", "World"]
	      return ACTION 
	       {
		anum = aid
		, statement = st
	       }	


