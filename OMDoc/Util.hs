{- |
Module      :  $Header$
Description :  Helper-functions
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

some utility functions
-}
module OMDoc.Util where

import Data.Char (isSpace)
import Data.List (isPrefixOf)
import Common.Utils

explodeNonEsc::String->String->[String]
explodeNonEsc _ [] = []
explodeNonEsc by s =
  let
    (i,r) = spanToNonEsc by s
  in
    [i] ++ explodeNonEsc by (drop (length by) r)

spanTo::forall a . Eq a => [a]->[a]->([a],[a])
spanTo _ [] = ([],[])
spanTo by list =
  if isPrefixOf by list
    then
      ([], list)
    else
      let
        (linit, lrest) = spanTo by (drop 1 list)
      in
        ((head list):linit, lrest)

spanToNonEsc::String->String->(String, String)
spanToNonEsc by s =
  let
    (maybeinit, mayberest) = spanTo by s
  in
    if (length maybeinit) == 0
      then
        (maybeinit, mayberest)
      else
        case mayberest of
          [] -> (maybeinit, mayberest)
          _ -> case (last maybeinit) of
            '\\' ->
              let
                (ni, nr) = spanToNonEsc by (drop 1 mayberest)
              in
                (maybeinit ++ (take 1 mayberest) ++ ni, nr)
            _ -> (maybeinit ,mayberest)

breakIf::forall a . (a->a->(Bool,Bool,Bool))->[a]->[[a]]
breakIf brkC l = _breakIf [] l
  where
  _breakIf::[a]->[a]->[[a]]
  _breakIf _ [] = []
  _breakIf i [a] = [i++[a]]
  _breakIf i (c:r) =
    let
      (doBreak, discardC1, discardC2) = brkC c (head r)
    in
      if doBreak
        then
          ([i ++ (if discardC1 then [] else [c])])
            ++ (_breakIf [] (if discardC2 then (drop 1 r) else r))
        else
          _breakIf (i++[c]) r


breakIfExt::forall a . (a->(Bool,Bool))->(a->a->(Bool,Bool,Bool))->[a]->[[a]]
breakIfExt brkS brkC l = _breakIfFst l
  where
  _breakIf::[a]->[a]->[[a]]
  _breakIf _ [] = []
  _breakIf i [c] = [i ++ [c]]
  _breakIf i (c:r) =
    let
      (doBreak, discardC1, discardC2) = brkC c (head r)
    in
      if doBreak
        then
          ([i ++ (if discardC1 then [] else [c])])
            ++ (_breakIfFst (if discardC2 then (drop 1 r) else r))
        else
          _breakIf (i++[c]) r

  _breakIfFst::[a]->[[a]]
  _breakIfFst [] = []
  _breakIfFst (c:r) =
    let
      (doBreak, discardS) = brkS c
    in
      if doBreak
        then
          (if discardS then [[]] else [[c]])
            ++ _breakIf [] r
        else
          _breakIf [] (c:r)

-- breaks if not escaped and removes char that caused break
breakIfNonEsc::[Char]->String->[String]
breakIfNonEsc chars =
  breakIfExt
    (\c -> (elem c chars, True))
    (\c1 c2 -> ((c1 /= '\\') && (elem c2 chars), False, True))

breakSepSpace::String->[String]
breakSepSpace =
  filter (not . null) . map trim .
      breakIfExt
        (\c -> (isSpace c, True))
        (\c1 c2 -> ((c1 /= '\\') && (isSpace c2), False, True))

breakOnce::forall a . (a->a->(Bool, Bool, Bool))->[a]->([a],[a])
breakOnce _ [] = ([],[])
breakOnce _ [a] = ([a], [])
breakOnce brkC (c:r) =
  let
    (doBreak, discardC1, discardC2) = brkC c (head r)
  in
    if doBreak
      then
        ( if discardC1 then [] else [c], if discardC2 then (drop 1 r) else r)
      else
        let
          (linit, lrest) = breakOnce brkC r
        in
          (c:linit, lrest)

-- breaks at first occurence and removes breaking char...
breakOnceNonEsc::[Char]->String->(String, String)
breakOnceNonEsc chars =
  breakOnce
    (\c1 c2 -> ((c1/='\\') && (elem c2 chars), False, True) )

initorall::forall a . [a]->[a]
initorall [i] = [i]
initorall l = init l

-- | like init but returns empty list for empty list (init raises exception)
initOrEmpty::forall a . [a]->[a]
initOrEmpty [] = []
initOrEmpty l = init l

singleitem::forall a . Int->[a]->[a]
singleitem _ [] = []
singleitem 0 _ = []
singleitem 1 (i:_) = [i]
singleitem n (_:r) = singleitem (n-1) r

ehead::forall a . String->[a]->a
ehead s [] = error ("ehead : " ++ s)
ehead _ l = head l

headorempty::forall a . [[a]]->[a]
headorempty [] = []
headorempty x = head x

tailorempty::forall a . [a]->[a]
tailorempty [] = []
tailorempty l = tail l

lastorempty::forall a . [a]->[a]
lastorempty [] = []
lastorempty l = [last l]

spanEsc::(Char->Bool)->String->(String, String)
spanEsc _  [] = ([],[])
spanEsc test s =
  fst $
  until
    (\(_, rest) ->
      (length rest) == 0
    )
    (\((oks, bads), rest) ->
      let
        (unesced, esced) = span (/='\\') rest
        (newok, newbad) = span test unesced
      in
        if (length newbad) > 0
          then
            ( (oks++newok, newbad ++ esced), "" )
          else
            ( (oks++newok++(take 2 esced), bads), drop 2 esced )
    )
    (("",""), s)

unesc::String->String
unesc [] = []
unesc s =
  let
    (shead, stail) = span (/='\\') s
  in
    shead ++ (take 1 $ drop 1 stail) ++ unesc (drop 2 stail)


anything::forall a . [Maybe a]->Maybe a
anything [] = Nothing
anything ((Just a):_) = Just a
anything (Nothing:r) = anything r

anythingOr::forall a . a->[Maybe a]->a
anythingOr a l =
  case anything l of
    Nothing -> a
    (Just x) -> x

makeTupel::forall a . [a]->[(a, a)]
makeTupel [] = []
makeTupel [_] = []
makeTupel (a:b:r) = (a,b):(makeTupel r)
