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
import Common.AS_Annotation as AS_Anno

negateFormula :: CMD -> CMD
negateFormula (Cmd s exps) = Cmd "Not" [(Op s [] exps nullRange)]


getAtoms :: EXPRESSION -> [String]
getAtoms e =
    case e of
      Var tk -> ["var:" ++ tokStr tk]
      Op s _ el _ -> ("op:" ++ s) : concatMap getAtoms el
      List el _ -> ("list") : concatMap getAtoms el
      Int i _ -> ["int"]
      Double d _ -> ["dbl"]

getCmdAtoms :: CMD -> [String]
getCmdAtoms c =
    case c of
      Cmd s el -> ("cmd:" ++ s) : concatMap getAtoms el
      Repeat e cl -> "repeat" : (getAtoms e ++ concatMap getCmdAtoms cl)


getBSAtoms :: BASIC_SPEC -> [String]
getBSAtoms (Basic_spec l) = concatMap (f . AS_Anno.item) l
    where f (Op_decl _) = []
          f (Axiom_item ac) = getCmdAtoms $ AS_Anno.item ac
