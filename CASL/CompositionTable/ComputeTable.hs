{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  portable

  Compute the composition table of a relational algebra that is
  specified in a particular way in a CASL theory.
-}

module CASL.CompositionTable.ComputeTable where

import CASL.CompositionTable.CompositionTable
import CASL.AS_Basic_CASL
import CASL.Sign
import Common.AS_Annotation
import Common.Id
import Common.PrettyPrint
import Common.Result
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

-- | given a specfication (name and theory), compute the composition table
computeCompTable :: SIMPLE_ID -> (Sign f e, [Named (FORMULA f)]) 
                       -> Result Table
computeCompTable spName (sig,sens) = do
  {- look for something isomorphic to
       sorts BaseRel < Rel
       ops 
         id	 : BaseRel;
	 0,1	 : Rel;	 	 
   	   inv__ : BaseRel -> BaseRel;
         __cmps__: BaseRel * BaseRel -> Rel;
	  compl__: Rel -> Rel;	
         __cup__ : Rel * Rel -> Rel, assoc, idem, comm, unit 1
     forall x:BaseRel
     . x cmps id = x
     . id cmps x = x
     . inv(id) = id
  -} 
  let name = showPretty spName ""
      errmsg = "cannot determine composition table of specification "++name
      errSorts = errmsg 
                   ++ "\nneed exactly two sorts s,t, with s<t, but found:\n"
                   ++ showPretty ((emptySign ()::Sign () ()) 
				     { sortSet = sortSet sig,
				       sortRel = sortRel sig }) ""
      errCmps ops = errmsg 
                   ++ "\nneed exactly one operation __cmps__: BaseRel * BaseRel -> Rel, but found:\n"
                   ++ showPretty ops "" 
      errCmpl ops = errmsg 
                   ++ "\nneed exactly one operation  compl__: Rel -> Rel, but found:\n"
                   ++ showPretty ops "" 
  -- look for sorts
  (baseRel,rel) <-
     case map Set.toList $ Rel.topSort $ sortRel sig of
       [[b],[r]] -> return (b,r)
       _ -> fail errSorts
  -- types of operation symbols
  let opTypes = concatMap (\ (o, ts) ->
                             map ( \ ty -> (ty, o) ) $ Set.toList ts)
                    $ Map.toList (opMap sig)
      idt    = OpType {opKind = Total, opArgs = [], opRes = baseRel}
      zerot  = OpType {opKind = Total, opArgs = [], opRes = rel}
      invt   = OpType {opKind = Total, opArgs = [baseRel], opRes = baseRel}
      cmpt   = OpType {opKind = Total, opArgs = [baseRel,baseRel], 
		       opRes = baseRel}
      complt = OpType {opKind = Total, opArgs = [rel], opRes = rel}
      cupt   = OpType {opKind = Total, opArgs = [rel,rel], opRes = rel}
  -- look for operation symbols
  let mlookup t = map snd $ filter (\(t',_) -> t==t') opTypes
  cmps <- case mlookup cmpt of
              [op] -> return op
              ops -> fail (errCmps ops)
  cmpl <- case mlookup complt of
              [op] -> return op
              ops -> fail (errCmpl ops)
  {- look for 
     forall x:BaseRel
     . x cmps id = x
     . id cmps x = x
     . inv(id) = id  -}
  -- let idaxioms idt = 
  --    [Quantification Universal [Var_decl [x] baseRel nullRange ....
  let ids = mlookup idt 
  let attrs = Table_Attrs {tableName = name,
                           tableIdentity = ""}
      compTable = Compositiontable []
      convTable = Conversetable []
      models = Models []
  return $ Table attrs compTable convTable models
