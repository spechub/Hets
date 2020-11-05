{- |
Module      :  ./DFOL/Comorphism.hs
Description :  Helper functions for the DFOL -> CASL translation
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module DFOL.Comorphism where

import Common.Id
import Common.AS_Annotation
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import Data.Maybe
import qualified Data.Set as Set
import qualified Data.HashMap.Lazy as Map

import DFOL.Sign
import DFOL.AS_DFOL
import DFOL.Morphism
import DFOL.Symbol

import qualified CASL.Sign as CASL_Sign
import qualified CASL.AS_Basic_CASL as CASL_AS
import qualified CASL.Morphism as CASL_Morphism

-- shorthand notation
nr :: Range
nr = nullRange

-- the unique sort
sort :: CASL_AS.SORT
sort = mkId [Token "Sort" nr]

-- the special bot symbol
botTok :: Token
botTok = Token "Bot" nr

bot :: CASL_AS.CASLTERM
bot = CASL_AS.Application (CASL_AS.Qual_op_name (mkId [botTok])
                          (CASL_AS.Op_type CASL_AS.Total [] sort nr) nr) [] nr

-- constructing a FOL type of the specified arity
folType :: Int -> [CASL_AS.SORT]
folType n = replicate n sort

-- signature map
sigMap :: Sign -> CASL_Sign.CASLSign
sigMap sig =
  foldr (sigMapH sig) caslSig2 symbols
  where caslSig2 = (CASL_Sign.emptySign ())
          { CASL_Sign.sortRel = Rel.insertKey sort Rel.empty
          , CASL_Sign.opMap = MapSet.insert (mkId [botTok])
              (CASL_Sign.sortToOpType sort) MapSet.empty }
        symbols = Set.toList $ getSymbols sig

sigMapH :: Sign -> NAME -> CASL_Sign.CASLSign -> CASL_Sign.CASLSign
sigMapH sig sym csig = case kind of
       SortKind -> csig
         { CASL_Sign.predMap = insSym (predTy $ arity + 1) predis }
       PredKind -> csig { CASL_Sign.predMap = insSym (predTy arity) predis }
       FuncKind -> csig
         { CASL_Sign.opMap = MapSet.insert (mkId [sym])
             (CASL_Sign.mkTotOpType (folType arity) sort)
             $ CASL_Sign.opMap csig }
  where predis = CASL_Sign.predMap csig
        insSym = MapSet.insert (mkId [sym])
        predTy = CASL_Sign.PredType . folType
        Just kind = getSymbolKind sym sig
        Just arity = getSymbolArity sym sig

-- generating axioms for a translated signature
generateAxioms :: Sign -> [Named CASL_AS.CASLFORMULA]
generateAxioms sig = predAx ++ funcAx ++ sortAx
                     where sorts = Set.toList $ getSymbolsByKind sig SortKind
                           funcs = Set.toList $ getSymbolsByKind sig FuncKind
                           preds = Set.toList $ getSymbolsByKind sig PredKind
                           sortAx = generateSortAxioms sig sorts
                           funcAx = generateFuncAxioms sig funcs
                           predAx = generatePredAxioms sig preds

-- generating axioms for translated predicate symbols
generatePredAxioms :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]
generatePredAxioms = concatMap . generatePredAxiomsH

generatePredAxiomsH :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generatePredAxiomsH sig p =
      [makeNamed ("gen_pred_" ++ show p) formula | not $ null argNames]
   where Just argNames = getArgumentNames p sig
         Just argTypes = getArgumentTypes p sig
         args = map makeVar argNames
         formula = makeForall
                     argNames
                     (CASL_AS.mkImpl
                        (CASL_AS.mkNeg (makeTypeHyps argTypes args sig))
                        (CASL_AS.mkNeg (makePredication p args sig)))

-- generating axioms for translated function symbols
generateFuncAxioms :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]
generateFuncAxioms = concatMap . generateFuncAxiomsH

generateFuncAxiomsH :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generateFuncAxiomsH sig f =
   if null argNames
      then [makeNamed ("gen_func_1_" ++ show f) formula0]
      else [makeNamed ("gen_func_1_" ++ show f) formula1,
            makeNamed ("gen_func_2_" ++ show f) formula2]
   where Just argNames = getArgumentNames f sig
         Just argTypes = getArgumentTypes f sig
         Just resultType = getReturnType f sig
         args = map makeVar argNames
         formula1 = makeForall
                      argNames
                      (CASL_AS.mkImpl
                         (CASL_AS.mkNeg (makeTypeHyps argTypes args sig))
                         (CASL_AS.mkStEq (makeApplication f args sig) bot))
         formula2 = makeForall
                      argNames
                      (CASL_AS.mkImpl
                         (makeTypeHyps argTypes args sig)
                         (makeTypeHyp resultType
                                      (makeApplication f args sig) sig))
         formula0 = makeTypeHyp resultType (makeApplication f [] sig) sig

-- generating axioms for translated sort symbols
generateSortAxioms :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]
generateSortAxioms sig ss =
  axioms1 ++ axioms2 ++ [axiom3] ++ axioms4
  where axioms1 = concatMap (generateSortAxiomsH1 sig) ss
        axioms2 = concatMap (generateSortAxiomsH2 sig) ss
        axiom3 = generateSortAxiomsH3 sig ss
        axioms4 = generateSortAxiomsH4 sig ss

generateSortAxiomsH1 :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generateSortAxiomsH1 sig s =
      [makeNamed ("gen_sort_1_" ++ show s) formula | not $ null argNames]
   where Just argNames = getArgumentNames s sig
         Just argTypes = getArgumentTypes s sig
         args = map makeVar argNames
         elName = Token "gen_y" nr
         el = makeVar elName
         formula = makeForall
                     argNames
                     (CASL_AS.mkImpl
                        (CASL_AS.mkNeg (makeTypeHyps argTypes args sig))
                        (makeForall
                           [elName]
                           (CASL_AS.mkNeg
                              (makePredication s (args ++ [el]) sig))))

generateSortAxiomsH2 :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generateSortAxiomsH2 sig s =
   if ar == 0
      then [makeNamed ("gen_sort_2_" ++ show s) formula0]
      else [makeNamed ("gen_sort_2_" ++ show s) formula1,
            makeNamed ("gen_sort_3_" ++ show s) formula2]
   where Just ar = getSymbolArity s sig
         argNames1 = makeArgNames "x" ar
         argNames2 = makeArgNames "y" ar
         elName = Token "z" nr
         args1 = map makeVar argNames1
         args2 = map makeVar argNames2
         el = makeVar elName
         formula1 = makeForall
                      argNames1
                      $ CASL_AS.mkNeg $ makePredication s (args1 ++ [bot]) sig
         formula2 = makeForall
                      (argNames1 ++ argNames2 ++ [elName])
                      $ CASL_AS.mkImpl
                         (CASL_AS.conjunct
                            [makePredication s (args1 ++ [el]) sig,
                             makePredication s (args2 ++ [el]) sig])
                         $ CASL_AS.conjunct
                            $ zipWith CASL_AS.mkStEq args1 args2
         formula0 = CASL_AS.mkNeg $ makePredication s [bot] sig

generateSortAxiomsH3 :: Sign -> [NAME] -> Named CASL_AS.CASLFORMULA
generateSortAxiomsH3 sig ss =
   makeNamed "gen_sort_4" formula
   where elName = Token "y" nr
         el = makeVar elName
         ar s = fromJust $ getSymbolArity s sig
         argNames s = makeArgNames "x" (ar s)
         args s = map makeVar (argNames s)
         formula = makeForall
                     [elName]
                     (CASL_AS.mkImpl
                        (CASL_AS.mkNeg (CASL_AS.mkStEq el bot))
                        (CASL_AS.disjunct $ map subformula ss))
         subformula s = if ar s == 0
                           then makePredication s [el] sig
                           else makeExists
                                  (argNames s)
                                  $ makePredication s (args s ++ [el]) sig

generateSortAxiomsH4 :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]
generateSortAxiomsH4 sig ss =
  map (generateSortAxiomsH4H sig) [ (s1, s2) | s1 <- ss, s2 <- ss, s1 < s2 ]

generateSortAxiomsH4H :: Sign -> (NAME, NAME) -> Named CASL_AS.CASLFORMULA
generateSortAxiomsH4H sig (s1, s2) =
   makeNamed ("gen_sort_5_" ++ show s1 ++ "_" ++ show s2) formula
   where Just ar1 = getSymbolArity s1 sig
         Just ar2 = getSymbolArity s2 sig
         argNames1 = makeArgNames "x" ar1
         argNames2 = makeArgNames "y" ar2
         elName = Token "z" nr
         args1 = map makeVar argNames1
         args2 = map makeVar argNames2
         el = makeVar elName
         formula = makeForall (argNames1 ++ argNames2 ++ [elName])
           $ CASL_AS.mkImpl (makePredication s1 (args1 ++ [el]) sig)
           $ CASL_AS.mkNeg $ makePredication s2 (args2 ++ [el]) sig
-- make argument names
makeArgNames :: String -> Int -> [NAME]
makeArgNames var n = map (\ i -> Token (var ++ "_" ++ show i) nr) [1 .. n]

-- make a variable
makeVar :: NAME -> CASL_AS.CASLTERM
makeVar var = CASL_AS.Qual_var var sort nr

-- make an application
makeApplication :: NAME -> [CASL_AS.CASLTERM] -> Sign -> CASL_AS.CASLTERM
makeApplication f as sig =
  CASL_AS.Application
    (CASL_AS.Qual_op_name
      (mkId [f])
      (CASL_AS.Op_type CASL_AS.Total (folType arity) sort nr)
      nr)
    as
    nr
  where Just arity = getSymbolArity f sig

-- make a predication
makePredication :: NAME -> [CASL_AS.CASLTERM] -> Sign -> CASL_AS.CASLFORMULA
makePredication p as sig =
  CASL_AS.Predication
    (CASL_AS.Qual_pred_name
       (mkId [p])
       (CASL_AS.Pred_type (folType arity1) nr)
       nr)
    as
    nr
  where Just kind = getSymbolKind p sig
        Just arity = getSymbolArity p sig
        arity1 = if kind == SortKind then arity + 1 else arity

-- make a universal quantification
makeForall :: [NAME] -> CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA
makeForall vars = CASL_AS.mkForall [CASL_AS.Var_decl vars sort nr]

-- make an existential quantification
makeExists :: [NAME] -> CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA
makeExists vars = CASL_AS.mkExist [CASL_AS.Var_decl vars sort nr]

-- make a type hypothesis
makeTypeHyp :: TYPE -> CASL_AS.CASLTERM -> Sign -> CASL_AS.CASLFORMULA
makeTypeHyp t term sig = makePredication s (args ++ [term]) sig
                         where Univ sortterm = t
                               (s, as) = termFlatForm sortterm
                               args = map (termTransl sig) as

-- make type hypotheses
makeTypeHyps :: [TYPE] -> [CASL_AS.CASLTERM]
                -> Sign -> CASL_AS.CASLFORMULA
makeTypeHyps ts terms sig =
  CASL_AS.conjunct $ map (\ (t, term) -> makeTypeHyp t term sig) $ zip ts terms

-- term translation
termTransl :: Sign -> TERM -> CASL_AS.CASLTERM
termTransl sig (Identifier x) = if not (isConstant x sig)
                                   then CASL_AS.Qual_var x sort nr
                                else makeApplication x [] sig
termTransl sig t = makeApplication f (map (termTransl sig) as) sig
                   where (f, as) = termFlatForm t

-- signature translation
sigTransl :: Sign -> (CASL_Sign.CASLSign, [Named CASL_AS.CASLFORMULA])
sigTransl sig = (sigMap sig, generateAxioms sig)

-- theory translation
theoryTransl :: (Sign, [Named FORMULA]) ->
                (CASL_Sign.CASLSign, [Named CASL_AS.CASLFORMULA])
theoryTransl (sig, fs) = (sigCASL, axCASL ++ fsCASL)
                        where (sigCASL, axCASL) = sigTransl sig
                              fsCASL = map (namedSenTransl sig) fs

-- morphism translation
morphTransl :: Morphism -> CASL_Morphism.CASLMor
morphTransl (Morphism sig1 sig2 sym_map) =
  foldl (addSymbolTransl sig1) init_morph $ Map.toList sym_map
  where init_morph = CASL_Morphism.Morphism
                       { CASL_Morphism.msource = fst $ sigTransl sig1
                       , CASL_Morphism.mtarget = fst $ sigTransl sig2
                       , CASL_Morphism.sort_map = Map.empty
                       , CASL_Morphism.op_map = Map.empty
                       , CASL_Morphism.pred_map = Map.empty
                       , CASL_Morphism.extended_map = ()
                       }

addSymbolTransl :: Sign -> CASL_Morphism.CASLMor -> (NAME, NAME) ->
                   CASL_Morphism.CASLMor
addSymbolTransl sig m (f, g) = case kind of
    FuncKind -> let
          f1 = (mkId [f], CASL_Sign.OpType CASL_AS.Partial (folType arity) sort)
          g1 = (mkId [g], CASL_AS.Total)
          in m {CASL_Morphism.op_map = Map.insert f1 g1
                $ CASL_Morphism.op_map m}
    PredKind -> let
          f1 = (mkId [f], CASL_Sign.PredType (folType arity))
          g1 = mkId [g]
          in m {CASL_Morphism.pred_map = Map.insert f1 g1
                $ CASL_Morphism.pred_map m}
    SortKind -> let
          f1 = (mkId [f], CASL_Sign.PredType (folType (arity + 1)))
          g1 = mkId [g]
          in m {CASL_Morphism.pred_map = Map.insert f1 g1
                $ CASL_Morphism.pred_map m}
  where Just kind = getSymbolKind f sig
        Just arity = getSymbolArity f sig

makeTypesAndVars :: [DECL] -> ([TYPE], [NAME], [CASL_AS.CASLTERM])
makeTypesAndVars ds = let varNames = getVarsFromDecls ds in
  ( concatMap (\ (ns, t1) -> replicate (length ns) t1) ds
  , varNames, map makeVar varNames)

-- sentence translation
senTransl :: Sign -> FORMULA -> CASL_AS.CASLFORMULA
senTransl sig frm = case frm of
    T -> CASL_AS.trueForm
    F -> CASL_AS.falseForm
    Pred t -> makePredication p (map (termTransl sig) as) sig
      where (p, as) = termFlatForm t
    Equality t1 t2 -> CASL_AS.mkStEq (termTransl sig t1) (termTransl sig t2)
    Negation f -> CASL_AS.mkNeg (senTransl sig f)
    Conjunction fs -> CASL_AS.conjunct (map (senTransl sig) fs)
    Disjunction fs -> CASL_AS.disjunct (map (senTransl sig) fs)
    Implication f g -> CASL_AS.mkImpl (senTransl sig f) (senTransl sig g)
    Equivalence f g -> CASL_AS.mkEqv (senTransl sig f) (senTransl sig g)
    Forall ds f -> let (types, varNames, vars) = makeTypesAndVars ds in
        makeForall varNames
             (CASL_AS.mkImpl (makeTypeHyps types vars sig) (senTransl sig f))
    Exists ds f -> let (types, varNames, vars) = makeTypesAndVars ds in
        makeExists varNames
             (CASL_AS.conjunct [makeTypeHyps types vars sig, senTransl sig f])

-- named sentence translation
namedSenTransl :: Sign -> Named FORMULA -> Named CASL_AS.CASLFORMULA
namedSenTransl sig nf = nf {sentence = senTransl sig $ sentence nf}

-- symbol translation
symbolTransl :: Sign -> Symbol -> Set.Set CASL_Sign.Symbol
symbolTransl sig sym =
  Set.singleton $ CASL_Sign.Symbol (mkId [n])
    $ case kind of
           PredKind -> CASL_Sign.PredAsItemType
                         $ CASL_Sign.PredType (folType arity)
           FuncKind -> CASL_Sign.OpAsItemType
                         $ CASL_Sign.mkTotOpType (folType arity) sort
           SortKind -> CASL_Sign.PredAsItemType
                         $ CASL_Sign.PredType (folType (arity + 1))
  where n = name sym
        Just kind = getSymbolKind n sig
        Just arity = getSymbolArity n sig
