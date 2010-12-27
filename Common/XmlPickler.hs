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
data PU a b = PU
  { pickle :: a -> b
  , unpickle :: b -> Result a }

puPrim :: (Show a, Read a) => PU a String
puPrim = PU
  { pickle = show
  , unpickle = \ s -> case readMaybe s of
        Nothing -> fail $ "unexpected text: " ++ s
        Just a -> return a
  }

puString :: PU String String
puString = PU
  { pickle = id
  , unpickle = return . id
  }

puWrap :: PU b c -> PU a b -> PU a c
puWrap pbc pab = PU
  { pickle = pickle pbc . pickle pab
  , unpickle = \ c ->
      unpickle pbc c >>= unpickle pab
  }

xpCData :: PU String Content
xpCData = PU
  { pickle = mkText
  , unpickle = \ c -> case c of
      Text d -> return $ cdData d
      _ -> fail $ "expected text instead of:\n" ++ ppContent c
  }

xpString :: PU String Content
xpString = puWrap xpCData puString

xpPrim :: (Show a, Read a) => PU a Content
xpPrim = puWrap xpCData puPrim

class XmlPickler a where
    xmlPickler :: PU a Content

instance XmlPickler String where
    xmlPickler = xpString

instance XmlPickler Int where
    xmlPickler = xpPrim

instance XmlPickler Integer where
    xmlPickler = xpPrim

puPair :: PU a b -> PU c d -> PU (a, c) (b, d)
puPair pab pcd = PU
  { pickle = \ (a, c) -> (pickle pab a, pickle pcd c)
  , unpickle = \ (b, d) -> joinResultWith (,) (unpickle pab b) $ unpickle pcd d
  }

tagContentList :: String -> PU [Content] Element
tagContentList tag = PU
  { pickle = unode tag
  , unpickle = \ e -> if qName (elName e) == tag then return $ elContent e
      else fail $ "expected <" ++ tag ++ "> element"
  }

elemToContent :: PU Element Content
elemToContent = PU
  { pickle = Elem
  , unpickle = \ c -> case c of
      Elem e -> return e
      _ -> fail $ "expected element instead of:\n" ++ ppContent c
  }

pairToList :: PU (a, a) [a]
pairToList = PU
  { pickle = \ (a, b) -> [a, b]
  , unpickle = \ l -> case l of
      [a, b] -> return (a, b)
      _ -> fail "expected two elements"
  }

xpPair :: String -> PU a Content -> PU b Content -> PU (a, b) Element
xpPair tag pua =
  puWrap (tagContentList tag) . puWrap pairToList . puPair pua

-- | unpickles last element first
puList :: PU a b -> PU [a] [b]
puList pab = PU
  { pickle = map (pickle pab)
  , unpickle = foldr (joinResultWith (:) . unpickle pab) $ return []
  }

xpList :: String -> PU a Content -> PU [a] Element
xpList tag = puWrap (tagContentList tag) . puList

-- | attribute pickler
xa :: PU a (b, [Attr]) -> PU b Element -> PU a Element
xa au pub = PU
  { pickle = \ a ->
      let (b, attrs) = pickle au a
      in add_attrs attrs $ pickle pub b
  , unpickle = \ e -> do
      b <- unpickle pub e
      unpickle au (b, elAttribs e)
  }
