module EVT.ParseEVT
        (
        evtBasicSpec
        , parseEVTGuards
        , parseEVTActions
        , parseGuard
        , parseAction
        )
        where

import Common.AnnoState
import Common.Id
import Text.ParserCombinators.Parsec
import Common.GlobalAnnotations (PrefixMap)
import Common.Token (sortId)

import CASL.AS_Basic_CASL
import qualified CASL.Formula as CASL

import EVT.AS 
import EVT.Keywords

evtBasicSpec :: PrefixMap -> AParser st MACHINE
evtBasicSpec _ = do spaces
--                  pos1 <- getPos
                    es <- many parseEVTEvents                    
--                  pos2 <- getPos
                    return (MACHINE es)

parseEVTEvents ::AParser st EVENT
parseEVTEvents =
        do
           try $ asKey event
           es <- parseEvent   
           return es

parseEvent ::AParser st EVENT
parseEvent =
        do
           name <- evtSortId
           spaces  
           gs <- many parseEVTGuards
           as <- many parseEVTActions
           return (EVENT name gs as)

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
              pr<-CASL.formula evtKeywords 
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
              st<- CASL.formula  evtKeywords 
              return ACTION 
               {
                anum = aid
                , statement = st
               }        


