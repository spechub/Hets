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

import Test
import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism 

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig = error "encodeSig not yet implemented"
{- todo
   setRel sig angucken
   Liste von Paaren (s,s') daraus generieren (siehe toList aus Common/Lib/Rel.hs)
   zurückgeben
   sig {opMap = ...     ein Id "_inj" mit Typmenge { s->s' | s<=s'}
                     +  ein Id "_proj" mit Typmegen {s'->?s | s<=s' }
        predMap = ...   pro s einen neuen Id "_elem_s" einfügen, mit entsprechender Typmenge ( alle  s' mit s<=s') 
       }

-}

generateAxioms :: Sign f e -> [Named (FORMULA f)]
generateAxioms sig = 
  concat 
   [inlineAxioms CASL
     "  sorts s < s' \
      \ op inj : s->s' \
      \ forall x,y:s . inj(x)=inj(y) => x=y  %(ga_embedding_injectivity)% "
          | (s,s') <- Rel.toList (sortRel sig)]
  where x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]

{- todo
  Axiome auf S. 407, oder RefMan S. 173

  einfacher evtl.: mit Hets erzeugen

library encode

spec sp =
       sorts s < s'
       op inj : s->s'
       op proj : s'->?s
       pred in_s : s'
       var x,y:s
       . inj(x)=inj(y) => x=y  %(ga_embedding_injectivity)%
end

und dann

sens <- getCASLSens "../CASL-lib/encode.casl"



*Main> sig <- getCASLSig "../CASL-lib/encode.casl"

<interactive>:1: Warning: Defined but not used: sig
Reading ../CASL-lib/encode.casl
Analyzing spec sp
Writing ../CASL-lib/encode.env
*Main> sig
Sign {sortSet = {s,s'}, sortRel = {(s,s')}, opMap = {inj:={OpType {opKind = Total, opArgs = [s], opRes = s'}}}, assocOps = {}, predMap = {}, varMap = {}, sentences = [], envDiags = [], extendedInfo = ()}
*Main> sens <- getCASLSens "../CASL-lib/encode.casl"

<interactive>:1: Warning: Defined but not used: sens
Reading ../CASL-lib/encode.casl
Analyzing spec sp
Writing ../CASL-lib/encode.env
*Main> sens
[NamedSen {senName = "ga_embedding_injectivity", sentence = Implication (Strong_equation (Sorted_term (Application (Qual_op_name inj (Total_op_type [s] s' []) []) [Sorted_term (Qual_var x s []) s []] []) s' []) (Sorted_term (Application (Qual_op_name inj (Total_op_type [s] s' []) []) [Sorted_term (Qual_var y s []) s []] []) s' []) [../CASL-lib/encode.casl:7.16]) (Strong_equation (Sorted_term (Qual_var x s []) s []) (Sorted_term (Qual_var y s []) s []) [../CASL-lib/encode.casl:7.28]) True [../CASL-lib/encode.casl:7.24]}]
*Main>

-}


encodeFORMULA :: Named (FORMULA f) -> Named (FORMULA f)
encodeFORMULA phi = error "encodeFORMULA not yet implemented"