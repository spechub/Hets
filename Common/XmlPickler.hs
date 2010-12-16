{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  xml pickler
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

xml pickler on top of the xml light package
-}

module Common.XmlPickler where

import Text.XML.Light
import Common.Result
import Common.ToXml
import Common.Utils

-- | the pickler data type (without a state)
data PU a = PU
  { pickleToContent :: a -> Content
  , unpickleContent :: Content -> Result a }

xpPrim :: (Show a, Read a) => PU a
xpPrim = PU
  { pickleToContent = mkText . show
  , unpickleContent = \ c -> case c of
      Text t -> let s = cdData t in case readMaybe s of
        Nothing -> fail $ "unexpected text: " ++ s
        Just a -> return a
      _ -> fail "expected primitive text data"
  }

xpString :: PU String
xpString = PU
  { pickleToContent = mkText
  , unpickleContent = \ c -> case c of
      Text t -> return $ cdData t
      _ -> fail "expected a string"
  }

class XmlPickler a where
    xmlPickler :: PU a

instance XmlPickler String where
    xmlPickler = xpString

instance XmlPickler Int where
    xmlPickler = xpPrim

instance XmlPickler Integer where
    xmlPickler = xpPrim

xpPair :: String -> PU a -> PU b -> PU (a, b)
xpPair tag pua pub =
  let err = fail $ "expected pair element with tag: " ++ tag
  in PU
  { pickleToContent = \ (a, b) ->
      Elem $ unode tag [pickleToContent pua a, pickleToContent pub b]
  , unpickleContent = \ c -> case c of
      Elem e -> case elContent e of
        [e1, e2] | qName (elName e) == tag -> do
          a <- unpickleContent pua e1
          b <- unpickleContent pub e2
          return (a, b)
        _ -> err
      _ -> err
  }

xpList :: String -> PU a -> PU [a]
xpList tag pua =
 let err = fail $ "expecting list element with tag: " ++ tag
 in PU
  { pickleToContent = Elem . unode tag . map (pickleToContent pua)
  , unpickleContent = \ c -> case c of
      Elem e -> if qName (elName e) == tag then
        mapM (unpickleContent pua) $ elContent e
        else err
      _ -> err
  }

-- | attribute pickler
data AU a b = AU
  { pickleToAttrs :: a -> [Attr]
  , stripAttrContent :: a -> b
  , unpickleAttrs :: b -> [Attr] -> Result a
  }

xa :: AU a b -> PU b -> PU a
xa au pub = PU
  { pickleToContent = \ a ->
      Elem $ add_attrs (pickleToAttrs au a)
        $ case pickleToContent pub (stripAttrContent au a) of
            Elem e -> e
            _ -> error "XmlPickler.xa"
  , unpickleContent = \ c -> case c of
      Elem e -> do
        b <- unpickleContent pub c
        unpickleAttrs au b $ elAttribs e
      _ -> fail "XmlPickler.xa"
  }
