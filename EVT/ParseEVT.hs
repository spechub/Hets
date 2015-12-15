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

evtBasicSpec :: PrefixMap -> AParser st EVENT
evtBasicSpec _ = do spaces
--                    pos1 <- getPos
                    gs <- many parseEVTGuards
                    as <- many parseEVTActions
--                    pos2 <- getPos
                    --error . show $ (EVENT (stringToId "FIXMEINPARSEEVT") gs as) 
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
              pr<-CASL.formula evtKeywords --this is what the csp people did
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
              st<- CASL.formula  evtKeywords --this is what the csp people did
              return ACTION 
               {
                anum = aid
                , statement = st
               }        


