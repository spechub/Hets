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
import List (nub,delete)

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig = sig {sortRel=newsortRel,opMap=priopMap,predMap=newpredMap}

  where 
 
 trivial=[(x,x)|x<-(fst(unzip(Rel.toList(sortRel sig))))++ snd(unzip(Rel.toList(sortRel sig)))] 
 relList=Rel.toList(sortRel sig)++nub(trivial) --[(SORT,SORT)] 
 newsortRel=Rel.fromList(relList)  --Rel SORT
 
 
 total      (s, s') = OpType {opKind=Total,opArgs=[s],opRes=s'}
 partial    (s, s') = OpType {opKind=Partial,opArgs=[s'],opRes=s}
 
   
 setinjOptype= Set.fromList(map total relList)  
 setproOptype= Set.fromList (map partial  relList)  
 injopMap=Map.insert inj setinjOptype (opMap sig) 
 priopMap=Map.insert pro setproOptype (injopMap)  
  
 inj=mkId[mkSimpleId "_inj"]
 pro=mkId[mkSimpleId "_proj"]

      --(SORT,[SORT])->[(SORT,[SORT])]
 --map 
 predList= nub(fst(unzip (relList)))
 udupredList=[(x,Set.toList(supersortsOf x sig))|x<-predList]  --[(SORT,[SORT])]
 altpredMap=predMap sig
 newcomb (x,[])=[ ]  --(SORT,[SORT])->[(SORT,[SORT])]
 newcomb  (x,(y:ys))=(x,[y]):(newcomb (x,ys))
 pred  x = PredType {predArgs=x} --[SORT]
 newpredMap = insertPred  newLList altpredMap 
 newLList=(concat(map newcomb udupredList)) --map (SORT,[SORT])->[(SORT,[SORT])]  [(SORT,[SORT])] [[(SORT,[SORT])]]
 --[(SORT,[SORT])]->Map.Map Id (Set.Set PredType)
 insertPred  [ ] m  = m
 insertPred  ((x,y):xs) m = insertPred (xs) (Map.insert (Id [mkSimpleId "_elem_"] [x] []) (Set.fromList[pred y]) m)

 
 
generateAxioms :: Sign f e -> [Named (FORMULA f)]
generateAxioms sig = 
  concat 
  ([inlineAxioms CASL
     "  sorts s < s' \
      \ op inj : s->s' \
      \ forall x,y:s . inj(x)=e=inj(y) => x=e=y   %(ga_embedding_injectivity)% "++
    inlineAxioms CASL
     " sort s< s' \
      \ op pr : s'->?s ; inj:s->s' \
      \ forall x:s . pr(inj(x))=e=x           %(projection)% " ++
    inlineAxioms CASL
      " sort s<s' \
      \ op pr : s'->?s \
      \ forall x,y:s'. pr(x)=e=pr(y)=>x=e=y   %(projection_transitiv)% " ++
    inlineAxioms CASL
      " sort s \
      \ op inj : s->s \
      \ forall x:s . inj(x)=e=x               %(indentity)%" ++
    inlineAxioms CASL
      " sort s<s' \
      \ op pr : s' -> ?s \
      \ forall x:s . x<=>def(pr(x))            %(mebership)%"                               
          | (s,s') <- rel2List])
      where 
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]
        pr=mkId [mkSimpleId "_pr"]
        pr_trans=mkId [mkSimpleId "_pr_trans"]
        indentity=mkId [mkSimpleId "_indentity"]
        membership=mkId[mkSimpleId "_membership"]
        rel2Map=Rel.toMap(sortRel sig)
        mapOp=Set.toList(opMap sig)
        rel2List=Rel.toList(sortRel sig)


{-
++               
   [inlineAxioms CASL
     " sort s<s';s'<s'' \
      \ op inj:s'->s'' ; inj: s->s' ; inj:s->s'' \
      \ forall x:s . inj(inj(x))=e=inj(x)      %(transitive)% "  
          |(s,s')<-rel2List,s''<-Set.toList(supersortsOf s' sig)]++
   [inlineAxioms CASL
    " sort s'<s ; s''<s ; w'_i ; w''_i ; w_i;  \
    \ op f:w'->s' ; f:w''->s'' ; inj: s' -> s ; inj: s''->s ; inj: s_i->s'_i ; inj:s_i -> s''_i \
    \ forall x_i : s_i . inj(f(inj(x_i)))=inj(f(inj(x_i))) \
    \ |(w,s,s',s'',w'_i,w''_i,f) | f<-mapOp, 
    
    " 
   
   
     ]





-}
        
        
    
        
