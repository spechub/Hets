-----------------------------------------------------------------------------
-- |
-- Module      :  Common.Lib.Parsec
-- Copyright   :  (c) Daan Leijen 1999-2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
-- 
-- Maintainer  :  daan@cs.uu.nl
-- Stability   :  provisional
-- Portability :  portable
--
-- Parsec, the Fast Monadic Parser combinator library, see
-- <http://www.cs.uu.nl/people/daan/parsec.html>.
--
-- Inspired by:
--
-- * Graham Hutton and Erik Meijer:
--   Monadic Parser Combinators.
--   Technical report NOTTCS-TR-96-4. 
--   Department of Computer Science, University of Nottingham, 1996. 
--   <http://www.cs.nott.ac.uk/Department/Staff/gmh/monparsing.ps>
--
-- * Andrew Partridge, David Wright: 
--   Predictive parser combinators need four values to report errors.
--   Journal of Functional Programming 6(2): 355-364, 1996
--
-- This helper module exports elements from the basic libraries.
--
-----------------------------------------------------------------------------

module Common.Lib.Parsec
               ( -- complete modules
                 module Text.ParserCombinators.Parsec) where 

import Text.ParserCombinators.Parsec

