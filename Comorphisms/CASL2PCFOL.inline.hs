{- 
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

--import Test
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
import CASL.Sublogic
import List (nub,delete)

-- | The identity of the comorphism
data CASL2PCFOL = CASL2PCFOL deriving (Show)

instance Language CASL2PCFOL -- default definition is okay

instance Comorphism CASL2PCFOL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol () where
    sourceLogic CASL2PCFOL = CASL
    sourceSublogic CASL2PCFOL = CASL_SL
                      { has_sub = True,
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2PCFOL = CASL
    targetSublogic CASL2PCFOL = CASL_SL
                      { has_sub = False, -- subsorting is coded out
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    map_sign CASL2PCFOL sig = let e = encodeSig sig in Just (e, [])
    map_morphism CASL2PCFOL = Just . id
    map_sentence CASL2PCFOL sig = Just -- needs to be improved !
    map_symbol CASL2PCFOL = Set.single . id

-- | Add injection, projection and membership symbols to a signature
encodeSig :: Sign f e -> Sign f e
encodeSig sig = sig {sortRel=newsortRel,opMap=priopMap,predMap=newpredMap}

  where 
 
 trivial=[(x,x)|x<-(fst(unzip(Rel.toList(sortRel sig))))++ snd(unzip(Rel.toList(sortRel sig)))] 
 relList=Rel.toList(sortRel sig)++nub(trivial) --[(SORT,SORT)] 
 newsortRel=Rel.fromList([])  --Rel SORT
 
 
 total      (s, s') = OpType {opKind=Total,opArgs=[s],opRes=s'}
 partial    (s, s') = OpType {opKind=Partial,opArgs=[s'],opRes=s}
 
   
 setinjOptype= Set.fromList(map total relList)  
 setproOptype= Set.fromList (map partial  relList)  
 injopMap=Map.insert inj setinjOptype (opMap sig) 
 priopMap=Map.insert pro setproOptype (injopMap)  
  
 inj=mkId[mkSimpleId "_inj"]
 pro=mkId[mkSimpleId "_proj"]

 predList= nub(fst(unzip (relList)))
 udupredList=[(x,Set.toList(supersortsOf x sig))|x<-predList] 
 oldpredMap=predMap sig
 pred  x = PredType {predArgs=x} 
 newList [ ] = [ ]
 newList (x:xs) = [[x]]++(newList xs)
 new1List (x,y) = (x,(newList y))
 nList = map new1List udupredList 
 predSet x  =  Set.fromList(map pred x) 
 eleminsert m (x,y)  = Map.insert (Id [mkSimpleId "_elem_"] [x] []) (predSet y) (m) 
 newpredMap  = foldl (eleminsert) (oldpredMap) (nList) 
 
 


{-
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
          | (s,s') <- rel2List]++             
   [inlineAxioms CASL
     " sort s<s';s'<s'' \
      \ op inj:s'->s'' ; inj: s->s' ; inj:s->s'' \
      \ forall x:s . inj(inj(x))=e=inj(x)      %(transitive)% "  
          |(s,s')<-rel2List,s''<-Set.toList(supersortsOf s' sig)]++
   [inlineAxioms CASL
    " sort s'<s ; s''<s ; w'_i ; w''_i ; w_i  \
    \ op f:w'->s' ; f:w''->s'' ; inj: s' -> s ; inj: s''->s ; inj: w_i->w'_i ; inj:w_i -> w''_i  \
    \ forall x_i : s_i . inj(f(inj(x_i)))=inj(f(inj(x_i)))  %(function_monotoniicity)%" 
          |(s,s'',s',w'_i,w''_i,w,f) | s<-(supersortOf s' sig),s1<-(supersortOf s'' sig),s1==s,
          w<-(supersortOf  w'_i sig),w1<-(supersortOf w''_i sig),w1==w,
          (w'_i,s')<-rel2List,(w''_i,s'')<-rel2List,(member f opSet)])
      where 
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]
        pr=mkId [mkSimpleId "_pr"]
        gaem_inj=mkId [mkSimpleId "ga_embedding_injectivity"]
        pr_trans=mkId [mkSimpleId "_pr_trans"]
        indentity=mkId [mkSimpleId "_indentity"]
        membership=mkId[mkSimpleId "_membership"]
        functionmono=mkId[mkSimpleId "_function-monotonicity"]
        rel2List=Rel.toList(sortRel sig)
        opSet=Set.fromList(elems(opMap sig))
        total      (s, s') = OpType {opKind=Total,opArgs=[s],opRes=s'}
        partial    (s, s') = OpType {opKind=Partial,opArgs=[s'],opRes=s}
        --isinopSet  x = member (Set.fromList [total x]) (opSet)
        --isproopSet x = member (Set.fromList [partial x]) (opSet)
        --rel2Map=Rel.toMap(sortRel sig)
        --mapOp=Set.toList(opMap sig)
-}

  {-
   [inlineAxioms CASL
   " sort w'_i ; w''_i ; w_i ; \
      


   ]






  -}

       
        
    
        
