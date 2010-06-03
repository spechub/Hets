{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}

module CSL.Tools where

import CSL.AS_BASIC_CSL
import Common.Id

negateFormula :: CMD -> CMD
negateFormula (Cmd s exps) = Cmd "Not" [(Op s exps nullRange)]

