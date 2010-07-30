{- |
Module      :  $Header$
Description :  static ADL analysis
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.StatAna where

import Adl.As
import Adl.Sign

import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
import Common.ExtSign
import Common.Id
import Common.GlobalAnnotations
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

basicAna :: ([PatElem], Sign, GlobalAnnos)
  -> Result ([PatElem], ExtSign Sign Relation, [Named Sen])
basicAna (ps, sig, _) =
  let (rs, ss) = foldr (\ p (r, s) ->
        case p of
          Pr u -> (r, makeNamed "" (Assertion u) : s)
          Pm qs d -> (d : r, map (\ q ->
                                 makeNamed (decnm d ++ "_" ++ showProp q)
                                 $ DeclProp d q) qs ++ s)
          _ -> (r, s)) ([], []) ps
  in return (ps, mkExtSign sig, ss)
