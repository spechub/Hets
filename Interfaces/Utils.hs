{- |
Module      :$Header$
Description : utilitary functions
Copyright   : uni-bremen and DFKI
License     : similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  : r.pascanu@jacobs-university.de
Stability   : provisional
Portability : portable

Interfaces.Utils contains different utilitary functions for the
abstract interface

-}

module Interfaces.Utils
         ( getAllNodes
         , getAllEdges
         , initNodeInfo
         , emptyIntIState
         ) where


import Interfaces.DataTypes
import GUI.GenericATPState
import Data.Graph.Inductive.Graph
import Static.DevGraph
import Proofs.AbstractState
import Logic.Logic
import Common.LibName

-- | Returns the list of all nodes, if it is not up to date
-- the function recomputes the list
getAllNodes :: IntIState  -> [LNode DGNodeLab]
getAllNodes st
 = labNodesDG $ lookupDGraph (i_ln st) (i_libEnv st)

-- | Returns the list of all edges, if it is not up to date
-- the funcrion recomputes the list
getAllEdges :: IntIState -> [LEdge DGLinkLab]
getAllEdges st
 = labEdgesDG $ lookupDGraph (i_ln st) (i_libEnv st)


-- | Constructor for CMDLProofGUIState datatype
initNodeInfo:: (Logic lid1 sublogics1
         basic_spec1 sentence1 symb_items1 symb_map_items1
         sign1 morphism1 symbol1 raw_symbol1 proof_tree1) =>
         ProofState lid1 sentence1 -> Int
         -> Int_NodeInfo
initNodeInfo ps nb
 = Element ps nb

emptyIntIState :: LibEnv -> LIB_NAME -> IntIState
emptyIntIState le ln =
  IntIState {
    i_libEnv = le,
    i_ln  = ln,
    elements = [],
    cComorphism = Nothing,
    prover = Nothing,
    consChecker = Nothing,
    save2file = False,
    useTheorems = False,
    script = ATPTactic_script {
                 ts_timeLimit = 20,
                 ts_extraOpts = [] },
    loadScript = False
    }


{--
conservativityRule :: DGRule
conservativityRule = DGRule "ConservativityCheck"

-- | check conservativity of the edge
checkconservativityEdge ::  LEdge DGLinkLab -> LibEnv ->
                              LIB_NAME ->
                            ([ConservativityChecker sign sentence morphism]
                            -> IO (Res.Result (conservativityChecker
                                      sign sentence morphism)))
                            ->  IO (String , LibEnv)
checkconservativityEdge (source,target,linklab) libEnv ln choser = do
  let libEnv' = case convertToNf ln libEnv target of
                  Result _ (Just lE) -> lE
                       -- replace error with some method to return it
                       -- (PGIP deals with error in its own way)
                  _ -> error "checkconservativityOfEdge: convertToNf"
  let (_, thTar) =
        case computeTheory True libEnv' ln target of
          Res.Result _ (Just th1) -> th1
              -- replace the error with something else ?
          _ -> error "checkconservativityOfEdge: computeTheory"
  G_theory lid _sign _ sensTar _ <- return thTar
  GMorphism cid _ _ morphism2 _ <- return $ dgl_morphism linklab
  Just (GMorphism cid' _ _ morphism3 _) <- return $
                  dgn_sigma $ labDG (lookupDGraph ln libEnv') target
  morphism2' <- coerceMorphism (targetLogic cid) lid
                "checkconservativityOfEdge2" morphism2
  morphism3' <- coerceMorphism (targetLogic cid') lid
                "checkconservativityOfEdge3" morphism3
  let compMor = case comp morphism2' morphism3' of
               Res.Result _ (Just phi) -> phi
                    -- replace error with something else ?
               _ -> error "checkconservativtiyOfEdge: comp"
  let (_le', thSrc) =
        case computeTheory False libEnv' ln source of
          Res.Result _ (Just th1) -> th1
               -- replace the error with something else ?
          _ -> error "checkconservativityOfEdge: computeTheory"
  G_theory lid1 sign1 _ sensSrc1 _ <- return thSrc
  sign2 <- coerceSign lid1 lid "checkconservativityOfEdge.coerceSign" sign1
  sensSrc2 <- coerceThSens lid1 lid "checkconservativityOfEdge1" sensSrc1
  let transSensSrc = propagateErrors
        $ mapThSensValueM (map_sen lid compMor) sensSrc2
  if length (conservativityCheck lid) < 1
   then
       do
        return ("No conservativity checkers available", libEnv')
   else
    do
     checkerR <- choser $ conservativityCheck lid
     if Res.hasErrors $ Res.diags checkerR
      then
       do
        return ("No conservativity checker chosen", libEnv')
      else
       do
        let chCons =  checkConservativity $
                      maybe (error "checkconservativityOfEdge4") id
                            $ Res.maybeResult $ checkerR
        let Res.Result ds res =
                chCons
                   (plainSign sign2, toNamedList sensSrc2)
                   compMor $ toNamedList
                               (sensTar `OMap.difference` transSensSrc)
            showObls [] = ""
            showObls obls = ", provided that the following proof obligations "
                            ++ "can be discharged:\n"
                            ++ concatMap (flip showDoc "\n") obls
            showRes = case res of
                       Just (Just (cst, obls)) -> "The link is "
                        ++ showConsistencyStatus cst ++ showObls obls
                       _ -> "Could not determine whether link is conservative"
            myDiags = showRelDiags 2 ds
--        createTextDisplay "Result of conservativity check"
--                        (showRes ++ "\n" ++ myDiags) [HTk.size(50,50)]
--        let
            consShow = case res of
                        Just (Just (cst, _)) -> cst
                        _                    -> Unknown "Unknown"
            GlobalThm proven conserv _ = dgl_type linklab
            consNew  = if ((show conserv) == (showToComply consShow))
                        then
                            Proven conservativityRule emptyProofBasis
                        else
                            LeftOpen
            provenEdge = (source
                         ,target
                         ,linklab
                          {
                            dgl_type = GlobalThm proven conserv consNew
                          }
                         )
            changes = [ DeleteEdge (source,target,linklab)
                      , InsertEdge provenEdge ]
            newGr = lookupDGraph ln libEnv'
            nextGr = changesDGH newGr changes
            newLibEnv = Map.insert ln
              (groupHistory newGr conservativityRule nextGr) libEnv'
        -- applyChanges actGraphInfo history
        return ( (showRes ++ "\n" ++ myDiags), newLibEnv)


--}
