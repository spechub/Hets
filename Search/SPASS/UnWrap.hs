{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
module Search.SPASS.UnWrap where

import Data.List as L (nubBy,partition)
import Data.Set (Set,empty,insert,union,unions,fromList,toList)
import Common.AS_Annotation
import SoftFOL.DFGParser
import SoftFOL.Sign
import SoftFOL.Print (printFormula)
import Text.ParserCombinators.Parsec
import Search.Common.Data
import Search.Common.Normalization --(normalize,Formula,Const,TrueAtom)
import Search.SPASS.FormulaWrapper (wrapTerm,SpassConst)
import Search.DB.Connection (multiInsertProfiles,insertStatistics,ProfileTuple)

 
type DFGSkeleton = Formula (Constant SpassConst) Int
type DFGFormula = (SPTerm, LineNr, Role)
type DFGParameter = String

-- (lib,theory,lineNr,spterm,skel,pars,role,strength)
type DFGProfile = Profile SPTerm DFGSkeleton DFGParameter

readDFGFormulae :: SourceName -> IO [DFGFormula]
readDFGFormulae file = (readProblem file) >>= (return . getDFGFormulae)

readProblem :: SourceName -> IO SPProblem
readProblem filePath =
    do result <- parseFromFile parseSPASS filePath
       case result 
         of Left err  -> error $ show err
	    Right spproblem  -> return spproblem

dfgNormalize (lib,theory) (spterm, lineNr, role) = 
    Profile lib theory lineNr spterm skel pars role strength
         where (skel,pars,strength) = normalize $ wrapTerm spterm


getDFGFormulae :: SPProblem -> [DFGFormula]
getDFGFormulae spproblem = concatMap unWrapFormulaList flsts
    where (SPProblem _ _ (SPLogicalPart _ _ flsts _ _) _) = spproblem

unWrapFormulaList :: SPFormulaList -> [DFGFormula]
unWrapFormulaList flst = map (toDFGFormula role) (formulae flst)
    where role = case originType flst
                 of SPOriginAxioms -> Axiom
                    SPOriginConjectures -> Theorem



toDFGFormula :: Role -> Named SPTerm -> (SPTerm, Int, Role)
toDFGFormula role sen = (spterm, lineNr, role)
    where spterm = unType $ sentence sen
          lineNr = read $ senAttr sen

unType :: SPTerm -> SPTerm
unType (SPSimpleTerm s) = (SPSimpleTerm s)
unType (SPComplexTerm s ts) = (SPComplexTerm s (map unType ts))
unType (SPQuantTerm q vs t) =
    let isSyimpleTerm (SPSimpleTerm _) = True
        isSyimpleTerm _ = False
    in case partition isSyimpleTerm vs
       of (vs',[]) -> SPQuantTerm q vs t
          (vs',tvs) -> SPQuantTerm q mergedVars (compose q)
              where vs'' = unions $ map (vars empty) tvs
                    mergedVars = toList $ union (fromList vs') vs''
                    wrapAnd [t] = t
                    wrapAnd ts = SPComplexTerm SPAnd tvs
                    compose SPForall = SPComplexTerm SPImplies [wrapAnd tvs, t]
                    compose SPExists = SPComplexTerm SPAnd (t:tvs)
                    compose _ = error "don't know how to untype this"

-- vars assumes quantifier free expressions
vars :: Set SPTerm -> SPTerm -> Set SPTerm
vars vs (SPSimpleTerm s) = insert (SPSimpleTerm s) vs
vars vs (SPComplexTerm _ ts) = unions $ (vs : (map (vars empty) ts))
vars _ _ = error "vars is not intended to handle quantified expressions."



f1 = "/home/immanuel/programming/casl/overloading_s1.dfg"
f2 = "/home/immanuel/dfg/query-files/test.dfg"


printDFGFormula (t,_,_) = printFormula $ makeNamed "" t
showTest = do [f] <- readDFGFormulae f2
              return $ printDFGFormula f