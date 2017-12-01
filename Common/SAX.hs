{- |
Module      :  ./Common/SAX.hs
Description :  A few helper functions to work with the sax parser
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  jonathan.von_schroeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module Common.SAX where

import Control.Monad
import Common.Lib.Maybe
import Common.Lib.State

import Text.XML.Expat.SAX
import qualified Data.ByteString.Lazy as L
import Data.Char

foldCatchLeft :: Monad m => (a -> MaybeT m a) -> a -> MaybeT m a
foldCatchLeft fn def = MaybeT $ do
 v <- runMaybeT $ fn def
 case v of
  Just res -> runMaybeT (foldCatchLeft fn res)
  _ -> return (Just def)

whileM :: Monad m => MaybeT m a -> MaybeT m [a]
whileM fn = liftM reverse $ foldCatchLeft (\ l -> liftM (: l) fn) []

type SaxEvL = [SAXEvent String String]
type DbgData = (Maybe [String], Bool)
type MSaxState a = MaybeT (State (SaxEvL, DbgData)) a

getM :: MSaxState (SaxEvL, DbgData)
getM = liftToMaybeT get

putM :: (SaxEvL, DbgData) -> MSaxState ()
putM = liftToMaybeT . put

debugS' :: String -> State (SaxEvL, DbgData) (Maybe a)
debugS' s = do
 (evl, (dbg, do_dbg)) <- get
 if do_dbg then do
  maybe (put (evl, (Just [s], do_dbg)))
        (\ msg -> put (evl, (Just $ s : msg, do_dbg)))
        dbg
  return Nothing
   else return Nothing

debugS :: String -> MSaxState a
debugS s = MaybeT $ debugS' s

runMSaxState :: MSaxState a -> SaxEvL -> Bool
                -> (Maybe a, (SaxEvL, DbgData))
runMSaxState f evl b = runState (runMaybeT f) (evl, (Nothing, b))

getD :: MSaxState SaxEvL
getD = liftM fst getM

putD :: SaxEvL -> MSaxState ()
putD evl = do
 (_, dbg) <- getM
 putM (evl, dbg)

parsexml :: L.ByteString -> SaxEvL
parsexml = parse defaultParseOptions

dropSpaces :: MSaxState ()
dropSpaces = do
 evl <- getD
 putD $ dropWhile
  (\ e ->
     case e of
      CharacterData d -> all isSpace d
      _ -> False
  ) evl

tag :: MSaxState (Bool, String)
tag = do
 dropSpaces
 d <- getD
 case d of
   [] -> error "Common.SAX.tag"
   h : xs -> do
     putD xs
     case h of
       StartElement s _ -> return (True, s)
       EndElement s -> return (False, s)
       _ -> debugS $ "Expected a tag - instead got: " ++ show h

expectTag :: Bool -> String -> MSaxState String
expectTag st s = do
 d <- getM
 MaybeT $ do
  v <- runMaybeT tag
  case v of
   Just p -> let p2 = (st, s) in if p2 /= p
                 then do
                  put d
                  debugS' $ "Expected tag " ++ show p2
                           ++ " but instead got: " ++ show p
                 else return $ Just s
   Nothing -> do
    put d
    debugS' "Expected a tag, but didn't find one - see previous message!"

readWithTag :: MSaxState a -> String -> MSaxState a
readWithTag fn tagName = do
 expectTag True tagName
 d <- fn
 expectTag False tagName
 return d

readL :: Show a => MSaxState a -> String -> MSaxState [a]
readL fn = readWithTag (whileM fn)

foldS :: Show a => (a -> MSaxState a) -> a -> String -> MSaxState a
foldS fn def = readWithTag (foldCatchLeft fn def)
