{- |
Module      :  ./CASL/CompositionTable/ComputeTable.hs
Description :  Compute the composition table of a relational algebra
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Compute the composition table of a relational algebra
  that isspecified in a particular way in a CASL theory.
-}

module CASL.CompositionTable.ComputeTable where

import CASL.CompositionTable.CompositionTable
import CASL.AS_Basic_CASL
import CASL.Sign

import Common.AS_Annotation
import Common.Id
import Common.IRI (IRI)
import Common.DocUtils
import Common.Result
import qualified Common.Lib.Rel as Rel
import qualified Control.Monad.Fail as Fail

import Data.Maybe
import qualified Data.Set as Set

-- | given a specfication (name and theory), compute the composition table
computeCompTable :: IRI -> (Sign f e, [Named (FORMULA f)])
                       -> Result Table
computeCompTable spName (sig, nsens) = do
  {- look for something isomorphic to
       sorts BaseRel < Rel
       ops
         id      : BaseRel;
         0,1     : Rel;
           inv__ : BaseRel -> BaseRel;
         __cmps__: BaseRel * BaseRel -> Rel;
          compl__: Rel -> Rel;
         __cup__ : Rel * Rel -> Rel, assoc, idem, comm, unit 1
     forall x:BaseRel
     . x cmps id = x
     . id cmps x = x
     . inv(id) = id
  -}
  let name = showDoc spName ""
      errmsg = "cannot determine composition table of specification " ++ name
      errSorts = errmsg
                   ++ "\nneed exactly two sorts s,t, with s<t, but found:\n"
                   ++ showDoc ((emptySign () :: Sign () ())
                                     { sortRel = sortRel sig }) ""
      errOps ops prof =
        errmsg ++ "\nneed exactly one operation " ++ prof ++ ", but found:\n"
               ++ showDoc ops ""
  -- look for sorts
  (baseRel, rel) <-
     case map Set.toList $ Rel.topSort $ sortRel sig of
       [[b], [r]] -> return (b, r)
       _ -> Fail.fail errSorts
  -- types of operation symbols
  let opTypes = mapSetToList (opMap sig)
      invt = mkTotOpType [baseRel] baseRel
      cmpt = mkTotOpType [baseRel, baseRel] rel
      complt = mkTotOpType [rel] rel
      cupt = mkTotOpType [rel, rel] rel
  -- look for operation symbols
  let mlookup t = map fst $ filter ((== t) . snd) opTypes
  let oplookup typ msg =
        case mlookup typ of
               [op] -> return op
               ops -> Fail.fail (errOps ops msg )
  cmps <- oplookup cmpt "__cmps__: BaseRel * BaseRel -> Rel"
  _cmpl <- oplookup complt "compl__: Rel -> Rel"
  inv <- oplookup invt "inv__ : BaseRel -> BaseRel"
  cup <- oplookup cupt "__cup__ : Rel * Rel -> Rel"
  {- look for
     forall x:BaseRel
     . x cmps id = x
     . id cmps x = x
     . inv(id) = id
  let idaxioms idt =
  [Quantification Universal [Var_decl [x] baseRel nullRange ....
  let ids = mlookup idt -}
  let sens = map (stripQuant . sentence) nsens
  let cmpTab sen = case sen of
       Equation (Application (Qual_op_name c _ _)
                        [Application (Qual_op_name arg1 _ _) [] _,
                         Application (Qual_op_name arg2 _ _) [] _] _)
                       Strong res _ ->
         if c == cmps
           then
            Just $ Cmptabentry
                   Cmptabentry_Attrs {
                      cmptabentryArgBaserel1 = Baserel (showDoc arg1 ""),
                      cmptabentryArgBaserel2 = Baserel (showDoc arg2 "") }
                   $ extractRel cup res
           else Nothing
       _ -> Nothing
  let invTab sen = case sen of
       Equation (Application (Qual_op_name i _ _)
                        [Application (Qual_op_name arg _ _) [] _] _)
                       Strong (Application (Qual_op_name res _ _) [] _) _ ->
         if i == inv
           then
            Just Contabentry {
                   contabentryArgBaseRel = Baserel (showDoc arg ""),
                   contabentryConverseBaseRel = [Baserel (showDoc res "")] }
           else Nothing
       _ -> Nothing
  let attrs = Table_Attrs
              { tableName = name
              , tableIdentity = Baserel "id"
              , baseRelations = []
              }
      compTable = Compositiontable (mapMaybe cmpTab sens)
      convTable = Conversetable (mapMaybe invTab sens)
      models = Models []
  return $ Table attrs compTable convTable (Reflectiontable []) models

stripQuant :: FORMULA f -> FORMULA f
stripQuant (Quantification _ _ f _) = stripQuant f
stripQuant f = f

extractRel :: Id -> TERM f -> [Baserel]
extractRel cup (Application (Qual_op_name cup' _ _) [arg1, arg2] _) =
  if cup == cup'
    then extractRel cup arg1 ++ extractRel cup arg2
    else []
extractRel _ (Application (Qual_op_name b _ _) [] _) =
  [Baserel (showDoc b "")]
extractRel _ _ = []
