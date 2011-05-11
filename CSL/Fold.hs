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
import CSL.AS_BASIC_CSL (EXPRESSION (..), CMD (..), OpDecl, EXTPARAM , APInt, APFloat, OPID)

data Record a b = Record
    { foldAss :: CMD -> OpDecl -> b -> a
    , foldCmd :: CMD -> String -> [b] -> a
    , foldSequence :: CMD -> [a] -> a
    , foldCond :: CMD -> [(b, [a])] -> a
    , foldRepeat :: CMD -> b -> [a] -> a

    , foldVar :: EXPRESSION -> Token -> b
    , foldOp :: EXPRESSION -> OPID -> [EXTPARAM] -> [b] -> Range -> b
    , foldList :: EXPRESSION -> [b] -> Range -> b
    , foldInterval :: EXPRESSION -> Double -> Double -> Range -> b
    , foldInt :: EXPRESSION -> APInt -> Range -> b
    , foldRat :: EXPRESSION -> APFloat -> Range -> b
    }

-- | Produces an error with given message on all entries. Use this if you
-- overwrite only the EXPRESSION part and you do not use the CMD part anyway
-- , e.g., if you use the record in foldTerm
emptyRecord :: String -> Record a b
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
           , foldRat = error s
           }

-- | The identity transformation
idRecord :: Record CMD EXPRESSION
idRecord =
    Record { foldAss = \ v _ _ -> v
           , foldCmd = \ v _ _ -> v
           , foldSequence = \ v _ -> v
           , foldCond = \ v _ -> v
           , foldRepeat = \ v _ _ -> v

           , foldVar = \ v _ -> v
           , foldOp = \ v _ _ _ _ -> v
           , foldList = \ v _ _ -> v
           , foldInterval = \ v _ _ _ -> v
           , foldInt = \ v _ _ -> v
           , foldRat = \ v _ _ -> v
           }

-- | Passes the transformation through the CMD part and is the identity
-- on the EXPRESSION part
passRecord :: Record CMD EXPRESSION
passRecord =
    idRecord { foldAss = \ _ -> Ass
             , foldCmd = \ _ -> Cmd
             , foldSequence = \ _ -> Sequence
             , foldCond = \ _ -> Cond
             , foldRepeat = \ _ -> Repeat
             }

-- | Passes the transformation through both, the CMD and the EXPRESSION part
passAllRecord :: Record CMD EXPRESSION
passAllRecord =
    passRecord { foldVar = \ _ -> Var
               , foldOp = \ _ -> Op
               , foldList = \ _ -> List
               , foldInterval = \ _ -> Interval
               , foldInt = \ _ -> Int
               , foldRat = \ _ -> Rat
               }

-- | Passes the transformation through the 'CMD' part by concatenating the
-- processed list from left to right and identity on expression part
listCMDRecord :: Record [a] EXPRESSION
listCMDRecord =
    idRecord { foldAss = \ _ _ _ -> []
             , foldCmd = \ _ _ _ -> []
             , foldSequence = \ _ -> concat
             , foldCond = \ _ -> concat . concatMap snd
             , foldRepeat = \ _ _ -> concat
             }

-- | Returns the first constant on the CMD part and the second
-- on the EXPRESSION part
constRecord :: a -> b -> Record a b
constRecord a b =
    Record { foldAss = \ _ _ _ -> a
           , foldCmd = \ _ _ _ -> a
           , foldSequence = \ _ _ -> a
           , foldCond = \ _ _ -> a
           , foldRepeat = \ _ _ _ -> a

           , foldVar = \ _ _ -> b
           , foldOp = \ _ _ _ _ _ -> b
           , foldList = \ _ _ _ -> b
           , foldInterval = \ _ _ _ _ -> b
           , foldInt = \ _ _ _ -> b
           , foldRat = \ _ _ _ -> b
           }

foldCMD :: Record a b -> CMD -> a
foldCMD r f = case f of
   Ass c def -> foldAss r f c $ foldTerm r def
   Cmd s l -> foldCmd r f s $ map (foldTerm r) l
   Sequence l -> foldSequence r f $ map (foldCMD r) l
   Cond l -> foldCond r f $ map cf l where
                     cf (x, y) = (foldTerm r x, map (foldCMD r) y)
   Repeat c l -> foldRepeat r f (foldTerm r c) $ map (foldCMD r) l

foldTerm :: Record a b -> EXPRESSION -> b
foldTerm r t = case t of
    Var tok -> foldVar r t tok
    Op s epl al rg -> foldOp r t s epl (map (foldTerm r) al) rg
    List l rg -> foldList r t (map (foldTerm r) l) rg
    Interval from to rg -> foldInterval r t from to rg
    Int i rg -> foldInt r t i rg
    Rat f rg -> foldRat r t f rg
