{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

static analysis of DL parts especially cardinalities, predefined datatypes 
and additional annottations
-}

{- todo:
    - check for declaration/definition of illegal sorts, operations 
      and prediacates (related to the topsort DATA and the predefined symbols)
    -check for illegal formulas related to DATA and with predefined symbols
    - check that every new sort, operation and prediacte is related to Thing 
      in the subject argument position (1st argument),
      all other arguments can be either below DATA or Thing
    

-}
module CASL_DL.StatAna where

import CASL_DL.AS_CASL_DL
import CASL_DL.Print_AS
import CASL_DL.Sign

import CASL.Sign
import CASL.MixfixParser
import CASL.StaticAna
import CASL.Utils
import CASL.AS_Basic_CASL
import CASL.ShowMixfix
import CASL.Overload
import CASL.Inject
import CASL.LiteralFuns

import Common.AS_Annotation
import Common.GlobalAnnotations
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Lib.State
import Common.Id
import Common.Result

import Debug.Trace

basicCASL_DLAnalysis :: (BASIC_SPEC () () DL_FORMULA,
		       Sign DL_FORMULA CASL_DLSign, GlobalAnnos)
		   -> Result (BASIC_SPEC () () DL_FORMULA,
			      Sign DL_FORMULA CASL_DLSign,
			      Sign DL_FORMULA CASL_DLSign,
			      [Named (FORMULA DL_FORMULA)])
basicCASL_DLAnalysis inp@(bs,sig,ga) = 
    basicAnalysis minDLForm (const return) 
             (const return) ana_Mix diffCASL_DLSign inp
 {-   case basicAnalysis minDLForm (const return) 
             (const return) diffCASL_DLSign inp of
    Result ds1 mr -> maybe (Result ds1 Nothing) callAna mr
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
    , checkMix = noExtMixfixDL
    , putInj = injDL_FORMULA
    }

type DLSign = Sign DL_FORMULA CASL_DLSign

-- |
-- static analysis of annotations
analyseAnnos :: GlobalAnnos -> Sign DL_FORMULA CASL_DLSign 
             -> BASIC_SPEC () () DL_FORMULA -> Result DLSign
analyseAnnos ga sig bs = 
    Result [Diag Warning "Analysis of Annotations not yet implemented" 
                 nullRange] 
           (Just $ {- extentedInfo -} sig)

injDL_FORMULA :: DL_FORMULA -> DL_FORMULA
injDL_FORMULA (Cardinality ct pn varTerm natTerm ps) =
    Cardinality ct pn (injT varTerm) (injT natTerm) ps
    where injT = injTerm injDL_FORMULA

mapDL_FORMULA :: DL_FORMULA -> DL_FORMULA
mapDL_FORMULA (Cardinality ct pn varTerm natTerm ps) =
    Cardinality ct pn (mapT varTerm) (mapT natTerm) ps 
    where mapT = mapTerm mapDL_FORMULA

resolveDL_FORMULA :: MixResolve DL_FORMULA
resolveDL_FORMULA ga ids (Cardinality ct pn varTerm natTerm ps) =
    do vt <- resMixTerm varTerm
       nt <- resMixTerm natTerm
       return $ Cardinality ct pn vt nt ps 
    where resMixTerm = resolveMixTrm mapDL_FORMULA 
                                     resolveDL_FORMULA ga ids

noExtMixfixDL :: DL_FORMULA -> Bool
noExtMixfixDL f =
    let noInner = noMixfixT noExtMixfixDL in
    case f of
    Cardinality _ _ t1 t2 _ -> noInner t1 && noInner t2

minDLForm :: Min DL_FORMULA CASL_DLSign
minDLForm sign form = 
    case form of
    Cardinality ct pn varTerm natTerm ps ->
        case Map.findWithDefault Set.empty pn (predMap sign) of
        pn_typeSet 
            | Set.null pn_typeSet -> 
                Result [Diag Error ("Unknown predicate: \""++
                                    show pn++"\"") (posOfId pn)]
                       Nothing
            | otherwise -> 
              let pn_RelTypes = Set.filter (\pt -> length (predArgs pt) == 2)
                                           pn_typeSet
              in if Set.null pn_RelTypes 
                 then Result [Diag Error ("No binary predicate \""++
                                    show pn++"\" declared") (posOfId pn)]
                       Nothing
                 else do
                   v2 <- oneExpTerm minDLForm sign varTerm
                   let v_sort = term_sort v2
                   n2 <- oneExpTerm minDLForm sign natTerm
                   let n_sort = term_sort n2
                       isRelSort = 
                           if v_sort `super_sort_of_subj` pn_RelTypes 
                           then [] 
                           else [Diag Error 
                                    ("Variable in cardinality constraint "++
                                     "has wrong type for predicate \""++
                                     show pn++"\"") 
                                    ps]
                       isNatTerm = 
                           if -- n_sort == "nonNegativeInteger" &&
                              isNumberTerm (globAnnos sign) n2
                           then []
                           else [Diag Error
                                    ("The second argument of a "++
                                     "cardinality constrain must be a "++
                                     "number literal typeable as "++
                                     "nonNegativeInteger\n"++show n2)
                                    ps]
                       ds = isRelSort ++ isNatTerm
                   appendDiags ds
                   if null ds
                    then return (Cardinality ct pn v2 n2 ps)
                    else Result [] Nothing
    where isNumberTerm ga t = 
              maybe False (uncurry (isNumber ga)) (splitApplM t)
          super_sort_of_subj v_sort typeSet =
              any (\ pt -> case predArgs pt of 
                           (s:_) -> s == v_sort || 
                                    Set.member v_sort (supersortsOf s sign)
                           _ -> error "CASL_DL.StatAna: false predicate"
                  ) $ Set.toList typeSet
