{- |
Module      :  $Header$
Copyright   :  (c) Zicheng Wang, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Coding out subsorting (SubPCFOL= -> PCFOL=), 
   following Chap. III:3.1 of the CASL Reference Manual
-}

{-
   testen mit
     make ghci
     :l Comorphisms/CASL2PCFOL.hs

   wenn es druch geht, dann in hets.hs einfügen
     import Comorphisms.CASL2PCFOL
   und dann einchecken, wenn es durch geht (make hets)
     cvs commit
-}

module Comorphisms.CASL2PCFOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

-- CASL
import CASL.Logic_CASL 
import qualified CASL.AS_Basic_CASL
import CASL.Sign
import qualified CASL.Morphism 

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig = ...
{- todo
   setRel sig angucken
   Liste von Paaren (s,s') daraus generieren (siehe toList aus Common/Lib/Rel.hs)
   zurückgeben
   sig {opMap = ...     ein Id "_inj" mit Typmenge { s->s' | s<=s'}
                     +  ein Id "_proj" mit Typmegen {s'->?s | s<=s' }
        predMap = ...   pro s einen neuen Id "_elem_s" einfügen, mit entsprechender Typmenge ( alle  s' mit s<=s') 
       }

-}

generateAxioms :: Sign f e -> [FORMULA f]
generateAxioms sig = ...
{- todo
  Axiome auf S. 407, oder RefMan S. 173
  z.B. embedding-injectivity
  Implication (ExistlEquation (Application (QualOpName ...) [QualVar "x" s] []) ()) (ExistlEquation (QualVar "x" s) (QualVar "y" s))
  einfacher evtl.: mit Hets erzeugen
    spec sp =
       sorts s < s'
       var x,y:s
       . inj(x)=inj(y) => x=y
    end
-}


encodeFORMULA :: 