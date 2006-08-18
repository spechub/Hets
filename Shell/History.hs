{- -*- Haskell -*-
 ----------------------------------------------------------------------------
 - History.hs - history implementation similar to GNU history
 ----------------------------------------------------------------------------
 - Copyright (C) 2000,2006  Michael Weber <michaelw@foldr.org>
 - 
 - All Rights Reserved.

 - Redistribution and use in source and binary forms, with or without
 - modification, are permitted provided that the following conditions are met:

 - - Redistribution of source code must retain the above copyright notice,
 - this list of conditions and the following disclamer.

 - - Redistribution in binary form must reproduce the above copyright notice,
 - this list of conditions and the following disclamer in the documentation
 - and/or other materials provided with the distribution.

 - THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS "AS IS" AND ANY
 - EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 - WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 - DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR THE CONTRIBUTORS BE LIABLE
 - FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 - DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 - SERVICES; LOSS OF USE, DATA OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 - CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 - OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE
 - USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 - 
 ----------------------------------------------------------------------------
 - Created:	2000-04-14
 - Last Update:	2000-09-17
 ----------------------------------------------------------------------------
 - NOTES:
 - * this module is far from complete, only the mostly needed functions are
 -   implemented.
 -
 - * the implementation does not really aim at efficiency...
 - 
 ----------------------------------------------------------------------------
 - TODO:
 - * document this file properly
 - 
 ----------------------------------------------------------------------------
 -}

module Shell.History 
  ( History      -- abstract
  , HistoryEntry
      ( AtTop    -- HistoryEntry a
      , Entry    -- a -> HistoryEntry a
      , AtBottom -- HistoryEntry a
      )             
  , removeEntry  -- History a -> History a
  , fromHistory  -- History a -> [a]
  , fromEntry    -- a -> HistoryEntry a -> a
  , insertEntry  -- a -> History a -> History a
  , movePos      -- Int -> History a -> History a
  , moveTop      -- History a -> History a
  , moveLast     -- History a -> History a
  , moveBottom   -- History a -> History a
  , replaceEntry -- a -> History a -> History a
  , currentEntry -- History a -> HistoryEntry a
  , addEntry     -- a -> History a -> History a
  , newHistory   -- History a
  , previous     -- History a -> History a
  , moveFirst    -- History a -> History a
  , numOfEntries -- History a -> Int
  , next         -- History a -> History a
  )
where

import List (init)


-------------------------------------------------------------------------------
data HistoryEntry a = AtTop | Entry a | AtBottom
    deriving (Show)


data History a = -- abstract
     History{ histHead  :: [HistoryEntry a] -- first entry at end of list
                                            -- current entry at beginning
            , histTail  :: [HistoryEntry a] -- last  entry at end of list
            }
    deriving (Show)


-------------------------------------------------------------------------------
fromEntry :: HistoryEntry a -> a
fromEntry (Entry e) = e


newHistory :: History a
newHistory = History{ histHead  = [AtTop]
                    , histTail  = [AtBottom]
                    }


addEntry :: a -> History a -> History a
addEntry newEntry = insertEntry newEntry . moveBottom


insertEntry :: a -> History a -> History a
insertEntry newEntry hist =
    case histHead hist of
      AtBottom : rest -> hist{ histHead = Entry newEntry : rest
                             , histTail = [AtBottom]
                             }
      hHead           -> hist{ histHead   = Entry newEntry : hHead }


replaceEntry :: a -> History a -> History a
replaceEntry newEntry hist =
    case histHead hist of
      AtTop : _       -> insertEntry newEntry hist
      AtBottom : rest -> insertEntry newEntry hist
      _ : rest        -> hist{ histHead   = Entry newEntry : rest }


removeEntry :: History a -> History a
removeEntry hist =
    case histHead hist of
      AtTop : _    -> hist
      AtBottom : _ -> hist
      _ : rest     -> hist{ histHead = rest }


movePos :: Int -> History a -> History a
movePos pos hist | pos >= 0 =
    let
      (h,t) = splitAt (pos+1) (reverse (histHead hist) ++ histTail hist)
    in
      hist{ histHead = reverse h
          , histTail = t
          }
movePos pos hist            = error "History.movePos: negative parameter `pos'"


moveTop :: History a -> History a
moveTop = movePos 0


moveFirst :: History a -> History a
moveFirst = next . moveTop


moveBottom :: History a -> History a
moveBottom hist =
    let
      hHead = histHead hist
      hTail = histTail hist
    in
      hist{ histHead = reverse hTail ++ hHead
          , histTail = []
          }


moveLast :: History a -> History a
moveLast = previous . moveBottom


numOfEntries :: History a -> Int
numOfEntries hist =
    length (histHead hist) + length (histTail hist) - 2


currentEntry :: History a -> HistoryEntry a
currentEntry = head . histHead


fromHistory :: History a -> [a]
fromHistory = map fromEntry . init . histTail . moveTop

next :: History a -> History a
next hist =
    case histTail hist of
      []     -> hist
      i:rest -> hist{ histHead = i : histHead hist
                    , histTail = rest
                    }


previous :: History a -> History a
previous hist =
    case histHead hist of
      []      -> error "History.previous: top sentinel missing"
      [AtTop] -> hist
      i:rest  -> hist{ histHead = rest
                     , histTail = i : histTail hist
                     }


isTop :: HistoryEntry a -> Bool
isTop AtTop = True
isTop _     = False


isBottom :: HistoryEntry a -> Bool
isBottom AtBottom = True
isBottom _        = False


-------------------------------------------------------------------------------
