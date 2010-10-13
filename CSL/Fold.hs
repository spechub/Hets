{- |
Module      :  $Header$
Description :  folding functions for CSL terms and commands
Copyright   :  (c) Ewaryst.Schulz, DFKI 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  portable

folding functions for CSL terms and commands

-}

module CSL.Fold where

import Common.Id
import CSL.AS_BASIC_CSL

data Record a b c = Record
    { foldAss :: c -> CMD -> b -> b -> a
    , foldCmd :: c -> CMD -> String -> [b] -> a
    , foldSequence :: c -> CMD -> [a] -> a
    , foldCond :: c -> CMD -> [(b, [a])] -> a
    , foldRepeat :: c -> CMD -> b -> [a] -> a

    , foldVar :: c -> EXPRESSION -> Token -> b
    , foldOp :: c -> EXPRESSION -> String -> [EXTPARAM] -> [b] -> Range -> b
    , foldList :: c -> EXPRESSION -> [b] -> Range -> b
    , foldInterval :: c -> EXPRESSION -> APFloat -> APFloat -> Range -> b
    , foldInt :: c -> EXPRESSION -> APInt -> Range -> b
    , foldDouble :: c -> EXPRESSION -> APFloat -> Range -> b
    }

emptyRecord :: String -> Record a b c
emptyRecord s =
    Record { foldAss = error s
           , foldCmd = error s
           , foldSequence = error s
           , foldCond = error s
           , foldRepeat = error s

           , foldVar = error s
           , foldOp = error s
           , foldList = error s
           , foldInterval = error s
           , foldInt = error s
           , foldDouble = error s
           }

idRecord :: Record CMD EXPRESSION c
idRecord =
    Record { foldAss = \ _ v _ _ -> v
           , foldCmd = \ _ v _ _ -> v
           , foldSequence = \ _ v _ -> v
           , foldCond = \ _ v _ -> v
           , foldRepeat = \ _ v _ _ -> v

           , foldVar = \ _ v _ -> v
           , foldOp = \ _ v _ _ _ _ -> v
           , foldList = \ _ v _ _ -> v
           , foldInterval = \ _ v _ _ _ -> v
           , foldInt = \ _ v _ _ -> v
           , foldDouble = \ _ v _ _ -> v
           }

constRecord :: a -> b -> Record a b c
constRecord a b =
    Record { foldAss = \ _ _ _ _ -> a
           , foldCmd = \ _ _ _ _ -> a
           , foldSequence = \ _ _ _ -> a
           , foldCond = \ _ _ _ -> a
           , foldRepeat = \ _ _ _ _ -> a

           , foldVar = \ _ _ _ -> b
           , foldOp = \ _ _ _ _ _ _ -> b
           , foldList = \ _ _ _ _ -> b
           , foldInterval = \ _ _ _ _ _ -> b
           , foldInt = \ _ _ _ _ -> b
           , foldDouble = \ _ _ _ _ -> b
           }

foldCMD :: Record a b c -> c -> CMD -> a
foldCMD r acc f = case f of
   Ass c def -> foldAss r acc f (foldTerm r acc c) $ foldTerm r acc def
   Cmd s l -> foldCmd r acc f s $ map (foldTerm r acc) l
   Sequence l -> foldSequence r acc f $ map (foldCMD r acc) l
   Cond l -> foldCond r acc f $ map cf l where
                     cf (x, y) = (foldTerm r acc x, map (foldCMD r acc) y)
   Repeat c l -> foldRepeat r acc f (foldTerm r acc c) $ map (foldCMD r acc) l

foldTerm :: Record a b c -> c -> EXPRESSION -> b
foldTerm r acc t = case t of
    Var tok -> foldVar r acc t tok
    Op s epl al rg -> foldOp r acc t s epl (map (foldTerm r acc) al) rg
    List l rg -> foldList r acc t (map (foldTerm r acc) l) rg
    Interval from to rg -> foldInterval r acc t from to rg
    Int i rg -> foldInt r acc t i rg
    Double f rg -> foldDouble r acc t f rg
