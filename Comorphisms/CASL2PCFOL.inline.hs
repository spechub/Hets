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
   todo
   predicate_monotonicity  (wie function_monotonicty)
   encodeFORMULA
   treat inj(u_i) separately
   map_morphism should modify sort_map etc.
   map_sign should avoid to generate OpNames with empty set of profiles
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
    map_theory CASL2PCFOL = mkTheoryMapping ( \ sig -> 
      let e = encodeSig sig in return (e, generateAxioms sig))
      (map_sentence CASL2PCFOL)
    map_morphism CASL2PCFOL mor = return 
      (mor  { msource =  encodeSig $ msource mor,
              mtarget =  encodeSig $ mtarget mor })
      -- other components need to be adapted as well!
    map_sentence CASL2PCFOL _ = return . f2Formula
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
 eleminsert m (x,y)  = Map.insert (membership x) (predSet y) (m) 
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
      \ forall x:s . pr(inj(x))=e=x           %(ga_projection)% " ++
    inlineAxioms CASL
      " sort s<s' \
      \ op pr : s'->?s \
      \ forall x,y:s'. pr(x)=e=pr(y)=>x=e=y   %(ga_projection_injectivity)% " ++
    inlineAxioms CASL
      " sort s \
      \ op inj : s->s \
      \ forall x:s . inj(x)=e=x               %(ga_identity)%" 
          | (s,s') <- rel2List]++
   [inlineAxioms CASL                
      " sort s<s' \
      \ op pr : s' -> ?s \
      \ pred mem : s' \
      \ forall x:s . mem(x) <=>def(pr(x))            %(ga_mebership)%"
          | (s,s') <- rel2List, let mem=membership s]++
   [inlineAxioms CASL
     " sort s<s';s'<s'' \
      \ op inj:s'->s'' ; inj: s->s' ; inj:s->s'' \
      \ forall x:s . inj(inj(x))=e=inj(x)      %(ga_transitivity)% "  
          |(s,s')<-rel2List,s''<-Set.toList(supersortsOf s' sig)] ++
   [inlineAxioms CASL
    " sort s'<s ; s''<s ; w'_i ; w''_i ; w_i; w_j  \
    \ ops f:w'_i->s' ; f:w''_i->s'' ; \
    \     inj: s' -> s ; inj: s''->s ; inj: w_i->w'_i ; inj:w_i -> w''_i  \
    \ var u_j : w_i   \
    \ forall u_i : w_i . \
    \ inj((op f:w'_i->s')(inj(u_j)))=inj((op f:w''_i->s'')(inj(u_j))) \
    \                                              %(ga_function_monotonicity)%"
    
          |(f,l)<- ftTL,t1<-l,t2<-l,length(opArgs t1)==length(opArgs t2),
           t1<t2,let w'=(opArgs t1),let w''=(opArgs t2),
           let s'=(opRes t1),let s''=(opRes t2),
           s<-Set.toList(supersortsOf s' sig),
           s1<-Set.toList(supersortsOf s'' sig),s1==s,
           w<- permute (map (findsubsort sig)  (zip w' w'')),
           let u = [mkSimpleId ("u"++show i) | i<-[1..length w]]   ]++
   [inlineAxioms CASL                                 
   " sort w'_i ; w''_i ; w_i  \ 
    \ pred p: w'_i;  pred p: w''_i;   inj:w_i->w'_i;   inj:w_i->w''_i \ 
    \ forall  v_i:w_i . (pred p:w'_i)(inj(v_i))=(pred p:w''_i)(inj(v_i)) \
    \                                           %(ga_predicate_monotonicity)%"
        | (f,l)<-pred2List, t1<-l, t2<-l, 
          length(predArgs t1)==length(predArgs t2),
          t1<t2, let w'=(predArgs t1), let w''=(predArgs t2), 
          w<-permute (map (findsubsort sig)  (zip w' w'')),
          let v = [mkSimpleId ("v"++show i) | i<-[1..length w]] ]) 

    where 
        x = mkSimpleId "x"
        y = mkSimpleId "y"
        inj = mkId [mkSimpleId "_inj"]
        pr=mkId [mkSimpleId "_pr"]
        gaem_inj=mkId [mkSimpleId "ga_embedding_injectivity"]
        pr_trans=mkId [mkSimpleId "_pr_trans"]
        indentity=mkId [mkSimpleId "_indentity"]
        functionmono=mkId[mkSimpleId "_function_monotonicity"]
        predmono=mkId[mkSimpleId "_predicate_monotonicity"]
        rel2List=Rel.toList(sortRel sig)
        pred2List = map   (\(x,y)->(x,Set.toList y))   (Map.toList(predMap sig))

        findsubsort   sig (x,y) = [s|s<-Set.toList(subsortsOf x sig),s1<-Set.toList(subsortsOf y sig),s1==s]
        ftTL= step1 sig     --[(Id,[OpType])]
        step1::Sign f e ->[(Id,[OpType])]
	step1  sig =map (\(x,y) -> (x,Set.toList y)) (Map.toList(opMap sig)) 

{- recursively go through the formula
   similar to CASL2Modal.hs
   replace Membership by:    Predication of "_elem_s"
   replace Cast by:          Application of "_pr"
-}


encodeFORMULA :: [Named (FORMULA f)] -> [Named (FORMULA f)]
encodeFORMULA  [ ]  = [ ]
encodeFORMULA  l = map nf2NFormula l


f2Formula::FORMULA f->FORMULA f
f2Formula  f = case f of
    Quantification q vs frm ps ->Quantification q vs (f2Formula frm) ps
    Conjunction fs ps ->  Conjunction (map f2Formula fs) ps
    Disjunction fs ps ->  Disjunction (map f2Formula fs) ps
    Implication f1 f2 b ps ->Implication (f2Formula f1) (f2Formula f2) b ps
    Equivalence f1 f2 ps ->  Equivalence (f2Formula f1) (f2Formula f2) ps
    Negation frm ps -> Negation (f2Formula frm) ps
    True_atom ps -> True_atom ps
    False_atom ps -> False_atom ps
    Existl_equation t1 t2 ps -> Existl_equation (t2term t1) (t2term t2) ps
    Strong_equation t1 t2 ps -> Strong_equation (t2term  t1) (t2term  t2) ps
    Predication pn as qs -> Predication pn (map t2term  as) qs
    Definedness t ps -> Definedness (t2term  t) ps
    Membership t ty ps -> Predication (Qual_pred_name (membership (ty)) (spos2PT t ps) ([]) ) [t2term t] ps
    Sort_gen_ax constrs isFree -> Sort_gen_ax constrs isFree
    _ -> error "FORMULA"


membership::SORT -> Id
membership t =Id [mkSimpleId ("_membership_"++show t)] [] []

spos2PT::TERM f -> [Pos] -> PRED_TYPE
spos2PT f pos =(Pred_type [(term2SSort f)] pos)


t2term::TERM f-> TERM f
t2term t = case t of
    Qual_var v ty ps -> Qual_var v ty ps
    Application opsym as qs  -> Application opsym (map t2term as) qs
    Sorted_term trm ty ps -> Sorted_term (t2term trm) ty ps
    Cast trm ty ps -> Application (projection trm ty) [t2term trm] ps
    Conditional t1 f t2 ps ->
       Conditional (t2term t1) f (t2term t2) ps
    _ -> error "TERM"

projection::TERM f -> SORT -> OP_SYMB
projection f s = (Qual_op_name pr (Op_type Partial [(term2SSort f)] s []) [])
  where
    pr=mkId [mkSimpleId "_pr"]




term2SSort::TERM f -> SORT
term2SSort t = case t of
      Sorted_term trm ty ps -> ty
      _ ->mkId[mkSimpleId ""]





nf2NFormula::Named (FORMULA f) -> Named (FORMULA f)
nf2NFormula nf = nf{
                    sentence=(f2Formula (sentence nf))
                    }


