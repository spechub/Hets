{-# OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances -cpp #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Serializer.Derive
-- Copyright   :  (c) Simon Foster 2006
-- License     :  GPL version 2 (see COPYING)
--
-- Maintainer  :  S.Foster@dcs.shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A Simple TH XMLData(+Data,Typeable) deriver for Algebraic Data-types.
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the
-- GNU General Public License as published by the Free Software Foundation; either version 2
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not,
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Text.XML.Serializer.Derive where

import Language.Haskell.TH
import Data.List
import Data.Char
import Data.Generics2
import Control.Monad
import Data.Maybe
import Text.XML.Serializer.Core
import Text.XML.Serializer.Datatypes
import Control.Monad
import Network.URI

data XCFilter = Decap

#ifndef __HADDOCK__
-- | Derive Data, Typeable and XMLData for the given data-type. Rather primitive at the moment, but should work for most data-types.
xmlifyPrim :: [ExpQ] -> Name -> Q [Dec]
xmlifyPrim funs name =
  do    info' <- reify name
        let ftr = foldr (\x -> \y -> [|(.)|] `appE` x `appE` y) [| id |] funs
        case info' of
           TyConI d -> do
             (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
             let typeQParams = map varT param
             let context = if (null typeQParams) then cxt []
                                                 else cxt $ map (conT ''Data `appT` (conT ''DictXMLData) `appT`) typeQParams
             funcs <- [d| toXMLType x = $ftr $ deriveXMLType x |]
             sequence [instanceD context (conT ''XMLData `appT` (foldl1 appT ([conT name] ++ typeQParams)))
                      (map return funcs)]
           _ -> do error "xmlify: Can only derive XMLData for data-type declarations"

qualify :: String -> Name -> Q [Dec]
qualify ns name =
  do    info' <- reify name
        case info' of
           TyConI d -> do
             (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
             let typeQParams = map varT param
             let context = cxt []
             funcs <- [d| namespaceURI _ = parseURI ns |]
             sequence [instanceD context (conT ''XMLNamespace `appT` (foldl1 appT ([conT name] ++ typeQParams)))
                      (map return funcs)]
           _ -> do error "qualify: Can only derive XMLNamespace for data-type declarations"

qualifyP :: [Name] -> String -> String -> Q [Dec]
qualifyP names ns p = mapM qual names >>= return . concat
  where qual name  = do info' <- reify name
                        case info' of
                          TyConI d -> do
                            (name, param, ca, terms) <- typeInfo ((return d) :: Q Dec)
                            let typeQParams = map varT param
                            let context = cxt []
                            funcs <- [d| namespaceURI _ = parseURI ns; defaultPrefix _ = p |]
                            sequence [instanceD context (conT ''XMLNamespace `appT` (foldl1 appT ([conT name] ++ typeQParams)))
                                     (map return funcs)]
                          _ -> do error "qualify: Can only derive XMLNamespace for data-type declarations"


-- | Prepare a data-type for serialization by deriving XMLData.
xmlify :: [Name] -> [ExpQ] -> Q [Dec]
xmlify names f = do x <- mapM (xmlifyPrim f) names >>= return . concat
                    d <- deriveCtx names ''DictXMLData
                    return $ d++x

-- | xmlify and qualify a list of data-types with the given namespace.
xmlifyQ :: [Name] -> [ExpQ] -> String -> Q [Dec]
xmlifyQ names f ns = do x <- mapM (xmlifyPrim f) names >>= return . concat
                        y <- mapM (qualify ns) names >>= return . concat
                        s <- deriveCtx names ''DictXMLData
                        return $ x++y++s

-- | xmlify with possible flags.
xmlifyF :: [(Name, [ExpQ])] -> [ExpQ] -> String -> Q [Dec]
xmlifyF names f ns = do x <- mapM (\(x, e) -> xmlifyPrim (e++f) x) names >>= return . concat
                        let nms = map fst names
                        y <- mapM (qualify ns) nms >>= return . concat
                        s <- deriveCtx nms ''DictXMLData
                        return $ x++y++s

-- | A sample flag, decapitalize all field names.
decapE     = [| decap |]
capE       = [| cap |]
capFieldsE = [| capFields |]
deusFieldsE = [| deusFields |]
removeFieldLeaderE = [| removeFieldLeader |]

idE   = [| id |]
attrE n = [| \x -> Attr occursOnce n Nothing |]
#endif
