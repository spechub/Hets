-- ------------------------------------------------------------

{- |
   Module     : Control.Arrow.ArrowState
   Copyright  : Copyright (C) 2005 Uwe Schmidt
   License    : MIT

   Maintainer : Uwe Schmidt
   Maintainer : uwe@fh-wedel.de
   Stability  : experimental
   Portability: portable
   Version    : $Id$

Arrows for managing an explicit state

State arrows work similar to state monads.
A state value is threaded through the application of arrows.

-}

-- ------------------------------------------------------------

module Control.Arrow.ArrowState
    ( ArrowState(..)
    )
where

import Control.Arrow

-- | The interface for accessing and changing the state component.
--
-- Multi parameter classes and functional dependencies are required.

class Arrow a => ArrowState s a | a -> s where

    -- | change the state of a state arrow by applying a function
    -- for computing a new state from the old and the arrow input.
    -- Result is the arrow input

    changeState		:: (s -> b -> s) -> a b b

    -- | access the state with a function using the arrow input
    -- as data for selecting state components.

    accessState		:: (s -> b -> c) -> a b c

    -- | read the complete state, ignore arrow input
    --
    -- definition: @ getState = accessState (\ s x -> s) @ 

    getState		:: a b s
    getState		= accessState (\ s _x -> s)

    -- | overwrite the old state
    --
    -- definition: @ setState = changeState (\ s x -> x) @
    setState		:: a s s
    setState		= changeState (\ _s x -> x)	-- changeState (const id)

-- ------------------------------------------------------------
