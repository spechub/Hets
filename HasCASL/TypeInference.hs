
{- HetCATS/HasCASL/TypeInference.hs
   $Id$
   Author:  Christian Maeder
   Year:    2002

   polymorphic type inference (with type classes) for terms

   limitiations:
   - no subtyping

   - ignore anonymous downsets as classes
   - an intersection class is a (flat) set of class names (without universe)

   - no mixfix analysis for types yet

   - ignore classes during type inference

   to do:
   - convert As.Type to Le.Type

   plan:
   - treat all arrows equal for unification and type inference
   - and also ignore lazy annotations!
  
   simply adapt the following

-- Part of `Typing Haskell in Haskell', version of November 23, 2000
-- Copyright (c) Mark P Jones and the Oregon Graduate Institute
-- of Science and Technology, 1999-2000
-- 
-- This program is distributed as Free Software under the terms
-- in the file "License" that is included in the distribution
-- of this software, copies of which may be obtained from:
--             http://www.cse.ogi.edu/~mpj/thih/

-}
module HasCASL.TypeInference where

import Control.Monad.State
import HasCASL.As
import HasCASL.Unify

type TIL = StateT (Subst, Int) []

-- do almost the same as in CASL.MixfixParser 
-- but filter out wrongly typed applications

-- makeAppl :: Type -> Id -> Maybe [Type] -> [Term] -> Term
-- get possible typings for an id applied to arguments 



