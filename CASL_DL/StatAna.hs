{- |
Module      :  ./CASL_DL/StatAna.hs
Description :  static analysis of DL parts
Copyright   :  (c) Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

static analysis of DL parts especially cardinalities, predefined datatypes
and additional annottations
-}

module CASL_DL.StatAna ( basicCASL_DLAnalysis
                       , minDLForm
                       , checkSymbolMapDL
                       , DLSign) where

import CASL_DL.AS_CASL_DL
import CASL_DL.Print_AS ()
import CASL_DL.Sign
import CASL_DL.PredefinedCASLAxioms

import CASL.Sign
import CASL.MixfixParser
import CASL.Morphism
import CASL.StaticAna
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Quantification

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.ConvertGlobalAnnos
import Common.DocUtils
import Common.Id
import Common.Result
import Common.ConvertLiteral
import Common.ExtSign
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

instance TermExtension DL_FORMULA where
    freeVarsOfExt sign (Cardinality _ _ t1 t2 mf _) =
        Set.union (freeTermVars sign t1) $ Set.union (freeTermVars sign t2)
           $ case mf of
               Nothing -> Set.empty
               Just f -> freeVars sign f

basicCASL_DLAnalysis
    :: (BASIC_SPEC () () DL_FORMULA, Sign DL_FORMULA CASL_DLSign, GlobalAnnos)
    -> Result (BASIC_SPEC () () DL_FORMULA,
               ExtSign (Sign DL_FORMULA CASL_DLSign) Symbol,
               [Named (FORMULA DL_FORMULA)])
basicCASL_DLAnalysis (bs, sig, ga) =
    do ga' <- mergeGlobalAnnos ga $ globAnnos predefSign
       let sig' = addSig addCASL_DLSign sig $ predefinedSign emptyCASL_DLSign
           bs' = transformSortDeclarations True bs
       case basicAnalysis minDLForm (const return)
             (const return) ana_Mix (bs', sig', ga') of
         r@(Result ds1 mr) ->
             maybe r (cleanStatAnaResult . postAna ds1 sig') mr

{- |
  True -> extend all sort declarations without a supersort
          with supersort Thing
  False -> remove Thing from all sort declarations with supersort Thing
-}
generateSubsorting :: Sign f e -> Sign f e
generateSubsorting sig =
    let
        inS = sortSet sig
        inR = sortRel sig
    in
      sig
      {
        sortRel = Set.fold (\ x y -> Rel.insertDiffPair x thing y) inR inS
      }

transformSortDeclarations :: Bool
                          -> BASIC_SPEC () () DL_FORMULA
                          -> BASIC_SPEC () () DL_FORMULA
transformSortDeclarations addThing (Basic_spec aBIs) =
    Basic_spec (processBIs aBIs)
    where processBIs = map (mapAn processBI)
          processBI bi = case bi of
                           Sig_items sig_i -> Sig_items (processSig_i sig_i)
                           _ -> bi
          processSig_i sig_i =
              case sig_i of
                Sort_items sk aSor_is r ->
                    Sort_items sk (concatMap processaSor_i aSor_is) r
                _ -> sig_i
          processaSor_i aSor_i =
              case processSor_i (item aSor_i) of
                [] -> []
                x : xs -> replaceAnnoted x aSor_i : map emptyAnno xs
          processSor_i sor_i =
              if addThing
              then
                    case sor_i of
                      Sort_decl sorts r ->
                          [Subsort_decl sorts thing r]
                      Subsort_decl _ supSort _
                          | supSort == thing -> [sor_i]
                          | otherwise ->
                              [ sor_i
                              , Subsort_decl [supSort] thing statAnaMarker]
                      _ -> [sor_i]
              else
                    case sor_i of
                      Subsort_decl sorts supSort r
                          | supSort == thing -> if r == statAnaMarker
                                                  then []
                                                  else [Sort_decl sorts r]
                          | otherwise -> [sor_i]
                      _ -> [sor_i]

-- | marker for sig items added to a basic spec
statAnaMarker :: Range
statAnaMarker = Range [SourcePos ">:>added for DL.StaticAna<:<" 0 0]

{- |
 * remove predefined symbols from a result of the static analysis

 * remove all explicit references of Thing from the BSIC_SPEC
-}
cleanStatAnaResult
    :: Result (BASIC_SPEC () () DL_FORMULA,
               ExtSign (Sign DL_FORMULA CASL_DLSign) Symbol,
               [Named (FORMULA DL_FORMULA)])
    -> Result (BASIC_SPEC () () DL_FORMULA,
               ExtSign (Sign DL_FORMULA CASL_DLSign) Symbol,
               [Named (FORMULA DL_FORMULA)])
cleanStatAnaResult r@(Result ds1 mr) = maybe r clean mr
    where clean (bs, ExtSign sig sys, sen) =
              Result ds1 (Just (transformSortDeclarations False bs
                               , ExtSign (generateSubsorting $ cleanSign sig) $
                                 Set.delete (idToSortSymbol thing) sys
                               , sen))
          cleanSign sig =
              diffSig diffCASL_DLSign sig $ predefinedSign emptyCASL_DLSign

{- |
  postAna checks the Signature for

  * all new sorts must be a proper subsort of Thing and
    must not be related to DATA

  * no new subsort relations with DATA

  * all new predicates must have a subsort of Thing as subject (1st argument)

  * all new operations must have a subsort of Thing as 1st argument

-}
postAna :: [Diagnosis]
        -> Sign DL_FORMULA CASL_DLSign
        -> (BASIC_SPEC () () DL_FORMULA,
            ExtSign (Sign DL_FORMULA CASL_DLSign) Symbol,
            [Named (FORMULA DL_FORMULA)])
        -> Result (BASIC_SPEC () () DL_FORMULA,
                   ExtSign (Sign DL_FORMULA CASL_DLSign) Symbol,
                   [Named (FORMULA DL_FORMULA)])
postAna ds1 in_sig i@(_, ExtSign acc_sig _, _) =
    Result (ds1 ++ ds_sig) $ if null ds_sig then Just i else Nothing
    where ds_sig = chkSorts ++ checkPreds ++ checkOps
          diff_sig = diffSig diffCASL_DLSign acc_sig in_sig
          chkSorts = Set.fold chSort [] (sortSet diff_sig) ++
             [Diag Error
                        ("\n     new subsort relations with data " ++
                         "topsort are not allowed") nullRange
             | Set.member dataS (supersortsOf thing acc_sig) ||
                 Set.member dataS (subsortsOf thing acc_sig) ||
                 supersortsOf dataS predefSign /=
                  supersortsOf dataS acc_sig ||
                 selectDATAKernel (sortRel predefSign)
                  /= selectDATAKernel (sortRel acc_sig)]
          chSort s ds = ds ++
              [mkDiag Error
                        ("\n     new sort is not a subsort of '" ++
                         showDoc thing "':") s
              | not $ Set.member thing $ supersortsOf s acc_sig]
              ++ [mkDiag Error
                        ("\n     new sort must not be a supersort of '" ++
                         showDoc thing "':") s
                 | Set.member thing (subsortsOf s acc_sig)]
          selectDATAKernel rel =
              Rel.intransKernel $ Rel.restrict rel $
                 Set.insert dataS
                        (subsortsOf dataS predefSign)

          checkPreds = MapSet.foldWithKey chPred [] (predMap diff_sig)
          chPred p ty = (chArgs "pred" p (predArgs ty) ++)
          checkOps = MapSet.foldWithKey chOp [] (opMap diff_sig)
          chOp o ty = (chArgs "op" o (opArgs ty) ++)
          chArgs kstr sym args =
              case args of
              [] -> if kstr == "op"
                    then []
                    else [mkDiag Error
                        "\n     propositional symbols are not allowed" sym]
              (s : _) ->
                  if s == thing ||
                     Set.member thing (supersortsOf s acc_sig)
                  then []
                  else [mkDiag Error
                        ("\n     the first argument sort of this " ++ kstr ++
                        " is not a subsort of '" ++ showDoc thing "':")
                        sym]


{- sketch of Annotation analysis:

    where callAna bsRes =
              case analyseAnnos ga acc_sig bs of
              Result ds2 mESig ->
                  maybe (Result (ds1++ds2) Nothing)
                        (integrateExt (ds1++ds2) baRes) mESig
          integrateExt ds (bs',dif_sig,acc_sig,sens) eSig =
              Result ds (bs',
                         dif_sig {extendedInfo = dif eSig (extendedInfo sig)},
                         acc_sig {extendedInfo = eSig},
                         sens)
-}

ana_Mix :: Mix () () DL_FORMULA CASL_DLSign
ana_Mix = emptyMix
    { putParen = mapDL_FORMULA
    , mixResolve = resolveDL_FORMULA
    }

type DLSign = Sign DL_FORMULA CASL_DLSign

mapDL_FORMULA :: DL_FORMULA -> DL_FORMULA
mapDL_FORMULA (Cardinality ct pn varTerm natTerm qualTerm ps) =
    Cardinality ct pn (mapT varTerm) (mapT natTerm) qualTerm ps
    where mapT = mapTerm mapDL_FORMULA

resolveDL_FORMULA :: MixResolve DL_FORMULA
resolveDL_FORMULA ga ids (Cardinality ct ps varTerm natTerm qualTerm ran) =
    do vt <- resMixTerm varTerm
       nt <- resMixTerm natTerm
       mf <- case qualTerm of
         Nothing -> return Nothing
         Just f -> fmap Just $
                   resolveMixFrm mapDL_FORMULA resolveDL_FORMULA ga ids f
       return $ Cardinality ct ps vt nt mf ran
    where resMixTerm = resolveMixTrm mapDL_FORMULA
                                     resolveDL_FORMULA ga ids

minDLForm :: Min DL_FORMULA CASL_DLSign
minDLForm sign form = case form of
    Cardinality ct ps varTerm natTerm qualTerm ran ->
       let pn = predSymbName ps
           pn_RelTypes = Set.filter isBinPredType
                 $ MapSet.lookup pn (predMap sign)
       in
      if Set.null pn_RelTypes then
                Result [Diag Error ("Unknown binary predicate: \"" ++
                                    show pn ++ "\"") (posOfId pn)]
                       Nothing
      else do
                   v2 <- oneExpTerm minDLForm sign varTerm
                   let v_sort = sortOfTerm v2
                   n2 <- oneExpTerm minDLForm sign natTerm
                   let n_sort = sortOfTerm n2
                   ps' <- case sub_sort_of_subj pn v_sort pn_RelTypes of
                          Result ds mts ->
                            let ds' =
                                 if null ds
                                 then [mkDiag Error
                                       ("Variable in cardinality constraint\n"
                                        ++ "    has wrong type")
                                       varTerm]
                                 else ds
                                amigDs ts =
                                 [Diag Error
                                  ("Ambiguous types found for\n    pred '" ++
                                   showDoc pn "' in cardinalty " ++
                                   "constraint: (showing only two of them)\n" ++
                                   "    '" ++ showDoc (head ts) "', '" ++
                                   showDoc (head $ tail ts) "'") ran]
                             in maybe (Result ds' Nothing)
                              (\ ts -> case ts of
                                [] -> error "CASL_DL.StatAna: Internal error"
                                [x] -> maybe
                                         (return $
                                            Qual_pred_name pn x nullRange)
                                         (\ pt -> if x == pt
                                                  then return ps
                                                  else noPredTypeErr ps)
                                         (getType ps)
                                _ -> maybe (Result (amigDs ts) Nothing)
                                           (\ pt -> if pt `elem` ts
                                                    then return ps
                                                    else noPredTypeErr ps)
                                           (getType ps))
                              mts
                   let isNatTerm =
                           if isNumberTerm (globAnnos sign) n2 &&
                              show n_sort == "nonNegativeInteger"
                           then []
                           else [mkDiag Error
                                    ("The second argument of a\n    " ++
                                     "cardinality constrain must be a " ++
                                     "number literal\n    typeable as " ++
                                     "nonNegativeInteger")
                                    natTerm]
                       ds = isNatTerm
                   appendDiags ds
                   if null ds
                    then return (Cardinality ct ps' v2 n2 qualTerm ran)
                    else Result [] Nothing
    where
          getType ps = case ps of
                        Pred_name _ -> Nothing
                        Qual_pred_name _ pType _ -> Just pType
          isNumberTerm ga t =
              maybe False (uncurry (isNumber ga)) (splitApplM t)

          noPredTypeErr ps = Result
              [mkDiag Error "no predicate with \n    given type found" ps]
              Nothing

          sub_sort_of_subj pn v_sort typeSet =
              foldl (\ (Result ds mv) pt ->
                         case predArgs pt of
                         (s : _)
                             | leqSort sign v_sort s ->
                                 maybe (Result ds $ Just [toPRED_TYPE pt])
                                       (\ l -> Result ds $
                                                   Just $ l ++ [toPRED_TYPE pt])
                                       mv
                             | otherwise ->
                                 Result ds mv
                         _ -> Result (ds ++ [mkDiag Error
                                                  ("no propositional " ++
                                                   "symbols are allowed\n    "
                                                   ++ "within cardinality " ++
                                                   "constraints")
                                                  pn]) mv
                  ) (Result [] Nothing) $ Set.toList typeSet

-- | symbol map analysis
checkSymbolMapDL :: RawSymbolMap -> Result RawSymbolMap
{- - implement a symbol mapping that forbids mapping of predefined symbols
       from emptySign
       use from Logic.Logic.Logic and from CASL:
          matches, symOf, statSymbMapItems
-}
checkSymbolMapDL rsm =
    let checkSourceSymbol sSym _ =
              if any (`matches` sSym) symOfPredefinedSign then
                  (sSym :) else id
        syms = Map.foldrWithKey checkSourceSymbol [] rsm
    in if null syms
       then return rsm
       else mkError "Predefined CASL_DL symbols cannot be mapped" syms

symOfPredefinedSign :: [Symbol]
symOfPredefinedSign = Set.toList . Set.unions $ symOf predefSign

isNumber :: GlobalAnnos -> Id -> [TERM f] -> Bool
isNumber = isGenNum splitApplM

splitApplM :: TERM f -> Maybe (Id, [TERM f])
splitApplM t = case t of
    Application {} -> Just $ splitAppl t
    _ -> Nothing

splitAppl :: TERM f -> (Id, [TERM f])
splitAppl t = case t of
              Application oi ts _ -> (op_id oi, ts)
              _ -> error "splitAppl: no Application found"

-- | extract the Id from any OP_SYMB
op_id :: OP_SYMB -> Id
op_id op = case op of
           Qual_op_name x _ _ -> x
           Op_name x -> x
