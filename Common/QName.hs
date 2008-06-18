{- |
Module      :  $Header$
Description :  a manual ShATermConvertible instance
Copyright   :  (c) C. Maeder, Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

an ShATermConvertible instance for QName from hxt
-}

module Common.QName () where

import Text.XML.HXT.DOM.QualifiedName (QName(QN))
import Common.ATerm.Lib
import Data.Char

instance ShATermConvertible QName where
    toShATermAux att0 (QN aa ab _) = do
        (att1, aa') <- toShATerm' att0 (aa ++ ":" ++ ab)
        return $ addATerm (ShAAppl (aa ++ ":" ++ ab) [aa'] []) att1
    fromShATermAux ix att = (att,
      case getShATerm ix att of
       ShAAppl idName _ _ ->
         if null idName || idName == "\"\"" then
              QN "" "_" ""
          else
           let idName' = read idName::String
               idName'' = if head idName' == '<' then
                               take ((length idName') -2) $ tail idName'
                             else idName'
               (pre, loc) = span (/= ':') idName''
           in if null loc then    -- no : in ID, only localName
                 QN "" pre ""
                 else
                  if (not $ isAlpha $ head pre)
                     then QN "" idName'' ""
                     else
                      if (take 4 pre == "http" ||
                          take 4 pre == "file")
                          then let (ns, loc2) = span (/= '#') idName''
                               in if length loc2 > 1 then
                                     QN "" (tail loc2) ns
                                     else QN "" ns ""
                          else  QN pre (tail loc) ""
       u -> fromShATermError "OWL.QName" u)
