{- |
Module      :  ./RigidCASL/Parse_AS.hs
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

Parser for rigid extension of CASL
-}

module RigidCASL.Parse_AS where

import CASL.Formula
import CASL.OpItem
import CASL.SortItem

import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import RigidCASL.AS_Rigid
import Text.ParserCombinators.Parsec

parseRigid :: AParser st ()
parseRigid = (asKey rigidS >> return ())

rigidSigItems :: AParser st R_SIG_ITEM
rigidSigItems =
    do    _r <- parseRigid  
          itemList hybrid_keywords sortS sortItem Rigid_sorts
            <|> itemList hybrid_keywords opS opItem Rigid_op_items
            <|> itemList hybrid_keywords predS predItem Rigid_pred_items

instance AParsable R_SIG_ITEM where
  aparser = rigidSigItems
