{-                                                                          
Module:  $Header: /repository/HetCATS/Comorphisms/PFOL2FOL.inline.hs,      v 
1.20 2004/06/02 19:52:39 mnd Exp $                                            
Copyright   :  (c) Zicheng Wang, Uni Bremen 2002-2004                         
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt          
                                                                               
Maintainer  :  hets@tzi.de                                                     
Stability   :  provisional                                                     
Portability :  portable                                                        
                                                                                
    
-}
module Comorphisms.PCFOL2FOL where

--import Test
import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation
--import Comorphisms.CASL2PCFOL


--CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic
import List (nub,delete)
import Common.ListUtils
import Data.List


sig2FOL::Sign f e-> Sign f e
sig2FOL  sig =sig {opMap=newOpMap,predMap=newpredMap }
 where
   sig2sort=Set.toList(sortSet sig)
   undef x = OpType{opKind = Total, opArgs=[],opRes=x}
   setundef = Set.fromList (map undef sig2sort)
   map2list = Map.toList(opMap sig)
   set2list = map (\(x,y)->(x,Set.toList y)) map2list
   par2total [] = []
   par2total (x:xs) = if ((opKind x)==Partial) then  (x{opKind=Total}):(par2total xs) else  x:(par2total xs)
   newTotalMap =Map.fromList [(x,Set.fromList(par2total y))|(x,y)<-set2list]
   bottom = mkId[mkSimpleId "_bottom"]
   newOpMap  = Map.insert bottom setundef newTotalMap
   d=mkId[mkSimpleId "_D"]
   undefpred x = PredType{predArgs=[x]}
   setundefpred = Set.fromList(map undefpred sig2sort)
   newpredMap = Map.insert d setundefpred (predMap sig)
 
{-
generateFOLAxioms:: Sign f e->[Named(FORMULAR f)]
generateFOLAxioms   sig = 
  concat
   ([inlineAxioms CASL 
      " sort s             \
      \ exits x:s._D(x)            %( )%
      |s<-sortList   ]) 
{-
     inlineAxioms CASL
      " sort s              \
      \ not _D(_bottom)     \       %( )%
      
        | s<-sortList ]) 
     
-}      
 where 
  sortList = Set.toList (sortSet sig)
  sortf s = Id [mkSimpleId "_bottom"] [s] [] 
  
-}   


