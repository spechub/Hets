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
import Common.ListUtils
import Data.List

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
    map_sign CASL2PCFOL sig = 
      let e = encodeSig sig in Just (e, generateAxioms sig)
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
      \ forall x,y:s'. pr(x)=e=pr(y)=>x=e=y   %(projection_transitivity)% " ++
    inlineAxioms CASL
      " sort s \
      \ op inj : s->s \
      \ forall x:s . inj(x)=e=x               %(identity)%" ++
    inlineAxioms CASL                
      " sort s<s' \
      \ op pr : s' -> ?s \
      \ forall x:s . x in s <=>def(pr(x))            %(mebership)%"                               
          | (s,s') <- rel2List]++

   [inlineAxioms CASL
     " sort s<s';s'<s'' \
      \ op inj:s'->s'' ; inj: s->s' ; inj:s->s'' \
      \ forall x:s . inj(inj(x))=e=inj(x)      %(transitive)% "  
          |(s,s')<-rel2List,s''<-Set.toList(supersortsOf s' sig)] ++
--s_i -> w_i
   [inlineAxioms CASL
    " sort s'<s ; s''<s ; w'_i ; w''_i ; w_i  \
    \ op f:w'_i->s' ; f:w''_i->s'' ; inj: s' -> s ; inj: s''->s ; inj: w_i->w'_i ; inj:w_i -> w''_i  \
    \ forall u_i : w_i . inj((op f:w'_i->s')(inj(u_i)))=inj((op f:w''_i->s'')(inj(u_i)))       %(function_monotonicity)%"
    
          |(f,l)<- ftTL,t1<-l,t2<-l,length(opArgs t1)==length(opArgs t2),
           t1<t2,let w'=(opArgs t1),let w''=(opArgs t2),let s'=(opRes t1),let s''=(opRes t2),
           s<-Set.toList(supersortsOf s' sig),s1<-Set.toList(supersortsOf s'' sig),s1==s,
           w<- permute (map (findsubsort sig)  (zip w' w'')),
           let u = [mkSimpleId ("u"++show i) | i<-[1..length w]]   ])
    where 
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]
        pr=mkId [mkSimpleId "_pr"]
        gaem_inj=mkId [mkSimpleId "ga_embedding_injectivity"]
        pr_trans=mkId [mkSimpleId "_pr_trans"]
        indentity=mkId [mkSimpleId "_indentity"]
        membership=mkId[mkSimpleId "_membership"]
        functionmono=mkId[mkSimpleId "_function_monotonicity"]
        rel2List=Rel.toList(sortRel sig)

        findsubsort::Sign f e-> (SORT,SORT)->[SORT]
        findsubsort   sig (x,y) = [s|s<-Set.toList(subsortsOf x sig),s1<-Set.toList(subsortsOf y sig),s1==s]

        findSubSort::Sign f e -> [(SORT,SORT)]->[[SORT]]
        findSubSort  _ [] = [] 
        findSubSort  sig (x:xs) = [(findsubsort sig x)]++(findSubSort sig xs)

        findw:: Sign f e-> [(SORT,SORT)]->[[SORT]]
        findw   sig l = permute (findSubSort sig l)  

        ftTL= step1 sig     --[(Id,[OpType])]
        


        step1::Sign f e ->[(Id,[OpType])]
	step1  sig =map (\(x,y) -> (x,Set.toList y)) (Map.toList(opMap sig)) 

        step2::[(Id,[OpType])]->[(Id,(OpType,OpType))]
        step2  [ ] = [ ] 
        step2  x = concat(map step2' x) 

        step2'::(Id,[OpType]) -> [(Id,(OpType,OpType))]
        step2'  (x,y) =[(f,(t1,t2)) | let f=x,t1<-y,t2<-y,not (t1==t2),t1<t2,length(opArgs t1)==length(opArgs t2) ]   

        step3::[(Id,(OpType,OpType))]-> [(Id,( ([SORT],SORT),([SORT],SORT) ) )]
        step3  [ ] = [ ]
        step3   l = map step31 l 
 
        step31:: (Id,(OpType,OpType)) -> (Id,(([SORT],SORT),([SORT],SORT)))
        step31  (f,(t1,t2)) = ( f, ( (opArgs t1,opRes t1) , (opArgs t2, opRes t2) ) ) 


        step4::Sign f e -> [(Id,( ([SORT],SORT),([SORT],SORT) ) )]-> [(Id, ([[SORT]],[SORT]))]
        step4 _ [ ] =  []
        step4 sig x =  step46 (sig)  (step43 sig x)

        step41 :: Sign f e -> SORT -> SORT -> [SORT]
        step41    sig s' s'' = [s|s<-Set.toList(supersortsOf s' sig),s1<-Set.toList(supersortsOf s'' sig),s1==s]

        step42:: Sign f e->(Id,(([SORT],SORT),([SORT],SORT)))->(Id,([(SORT,SORT)],[SORT]))
        step42   sig (f,((t1a,t1r),(t2a,t2r))) = (f,( ((zip t1a t2a),(step41 sig t1r t2r)) ))

        step43:: Sign f e -> [(Id,(([SORT],SORT),([SORT],SORT)))] -> [( Id,([(SORT,SORT)],[SORT]) ) ]
        step43   _  [ ]  = [ ]
        step43   sig l = map (step42 sig) (l)

        step44:: Sign f e -> (SORT,SORT)-> [SORT]
        step44   sig (w', w'') = [w|w<-Set.toList(subsortsOf w' sig),w1<-Set.toList(subsortsOf w'' sig),w1==w]

        step45:: Sign f e -> [(SORT,SORT)] -> [[SORT]]
        step45   _ [ ] = [ ] 
        step45   sig l = map (step44 sig) l

        step46:: Sign f e -> [( Id,([(SORT,SORT)],[SORT]) ) ]  -> [(Id, ([[SORT]],[SORT]))]
        step46   _ [] = [] 
        step46  sig ((f,(wl,sl)):xs ) = (f,((step45 sig wl),sl)):(step46 sig xs)

        step5:: [(Id, ([[SORT]],[SORT]))]-> [(Id, ([[SORT]],[SORT]))]
        step5   [ ] =   [ ]
        step5   l  = map step51 l   

        step51::(Id, ([[SORT]],[SORT]))->(Id,([[SORT]],[SORT]))
        step51  (f,(x,y)) = (f,((permute x),y) )

        step13::Sign f e-> [(Id,( ([SORT],SORT),([SORT],SORT) ) )]
        step13  sig = step3(step2 (step1 sig))

        step15::Sign f e ->  [(Id, ([[SORT]],[SORT]))]
        step15  sig = step5 (step4 sig (step13 sig))      
   
        result=step15 sig  --[(Id, ([[SORT]],[SORT]))]

 

 

       
        
    
        
