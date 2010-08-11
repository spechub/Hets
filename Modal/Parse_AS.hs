{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Wiebke Herding, C. Maeder, Uni Bremen 2004
License     :  GPLv2 or higher

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser for modal logic extension of CASL
-}

module Modal.Parse_AS where

import Common.AnnoState
import Common.AS_Annotation
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import Modal.AS_Modal
import Text.ParserCombinators.Parsec
import CASL.Formula
import CASL.OpItem

modal_reserved_words :: [String]
modal_reserved_words = diamondS:termS:rigidS:flexibleS:modalityS:[modalitiesS]

modalFormula :: AParser st M_FORMULA
modalFormula =
    do o <- oBracketT
       m <- modality []
       c <- cBracketT
       f <- primFormula modal_reserved_words
       return (BoxOrDiamond True m f $ toRange o [] c)
    <|>
    do o <- asKey lessS
       m <- modality [greaterS] -- do not consume matching ">"!
       c <- asKey greaterS
       f <- primFormula modal_reserved_words
       return (BoxOrDiamond False m f $ toRange o [] c)
    <|>
    do d <- asKey diamondS
       f <- primFormula modal_reserved_words
       let p = tokPos d
       return (BoxOrDiamond False (Simple_mod $ Token emptyS p) f p)

modality :: [String] -> AParser st MODALITY
modality ks =
    do t <- term (ks ++ modal_reserved_words)
       return $ Term_mod t
   <|> return (Simple_mod $ mkSimpleId emptyS)

instance AParsable M_FORMULA where
  aparser = modalFormula

rigor :: AParser st RIGOR
rigor = (asKey rigidS >> return Rigid)
        <|> (asKey flexibleS >> return Flexible)

rigidSigItems :: AParser st M_SIG_ITEM
rigidSigItems =
    do r <- rigor
       do itemList modal_reserved_words opS opItem (Rigid_op_items r)
         <|> itemList modal_reserved_words predS predItem (Rigid_pred_items r)

instance AParsable M_SIG_ITEM where
  aparser = rigidSigItems

mKey :: AParser st Token
mKey = asKey modalityS <|> asKey modalitiesS

mBasic :: AParser st M_BASIC_ITEM
mBasic =
    do (as, fs, ps) <- mItem simpleId
       return (Simple_mod_decl as fs ps)
    <|>
    do t <- asKey termS
       (as, fs, ps) <- mItem (sortId modal_reserved_words)
       return (Term_mod_decl as fs (tokPos t `appRange` ps))

mItem :: AParser st a -> AParser st ([Annoted a], [AnModFORM], Range)
mItem pr = do
       c <- mKey
       (as, cs) <- separatedBy (annoParser pr) anComma
       let ps = catRange $ c : cs
       do o <- oBraceT
          (fs, qs) <- annoParser (formula modal_reserved_words)
                      `separatedBy` anSemi
          p <- cBraceT
          return (as, fs, ps `appRange` toRange o qs p)
        <|>  return (as, [], ps)

instance AParsable M_BASIC_ITEM where
  aparser = mBasic
