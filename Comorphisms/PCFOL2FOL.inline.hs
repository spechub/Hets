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
import Comorphisms.CASL2PCFOL


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
sig2FOL  sig =sig {opMap=newopMap,predMap=newpredMap }
 where
   -- [SORT] 
   oldmap = opMap sig
   sig2sort=Set.toList(sortSet sig)
   undef x = OpType{opKind = Total, opArgs=[],opRes=x}
   setundef = Set.fromList (map undef sig2sort)
   map2list = Map.toList(opMap sig)
   set2list = map (\(x,y)->(x,Set.toList y)) map2list
   op2Total op = OpType{opKind=Total}
   botton = mkId[mkSimpleId "_Botton"]
   par2total (x,y)=if ((opKind (head y))==Partial) then (botton,( map op2Total y)) else (x,y)
   newop= map par2total set2list
   newpar = concat [y|(x,y)<-newop,(x==botton)]
   newopMap = (Map.insert botton (Set.fromList(newpar)) (Map.insert botton setundef oldmap ))
   d=mkId[mkSimpleId "_D"]
   undefpred x = PredType{predArgs=[x]}
   setundefpred = Set.fromList(map undefpred sig2sort)
   newpredMap = Map.insert d setundefpred (predMap sig) 




