{- |
Module      :  $Header$
Description :  Helper functions for the DFOL -> CASL translation
-}

module DFOL.Comorphism where

import Common.Id
import Common.AS_Annotation
import Common.Result
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map

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
folType n = take n $ repeat sort

-- signature map
sigMap :: Sign -> CASL_Sign.CASLSign
sigMap sig = 
  sigMapH symbols sig caslSig2
  where caslSig1 = CASL_Sign.emptySign ()
        caslSig2 = caslSig1 {CASL_Sign.sortSet = Set.singleton sort, 
                             CASL_Sign.opMap = Map.singleton (mkId [botTok])
                                                  $ Set.singleton 
                                                  $ CASL_Sign.OpType 
                                                       CASL_AS.Total [] sort}
        symbols = Set.toList $ getSymbols sig

sigMapH :: [NAME] -> Sign -> CASL_Sign.CASLSign -> CASL_Sign.CASLSign
sigMapH [] _ csig = csig
sigMapH (sym:syms) sig csig = 
  case kind of 
       SortKind -> 
         let predis = CASL_Sign.predMap csig
             predi = Map.singleton (mkId [sym]) $ Set.singleton
                                                $ CASL_Sign.PredType
                                                $ folType (arity+1)
             in sigMapH syms sig 
                 $ csig {CASL_Sign.predMap = CASL_Sign.addMapSet predis predi}
       PredKind -> 
         let predis = CASL_Sign.predMap csig
             predi = Map.singleton (mkId [sym]) $ Set.singleton
                                                $ CASL_Sign.PredType
                                                $ folType arity  
             in sigMapH syms sig 
                 $ csig {CASL_Sign.predMap = CASL_Sign.addMapSet predis predi} 
       FuncKind -> 
         let funcs = CASL_Sign.opMap csig
             func = Map.singleton (mkId [sym]) $ Set.singleton
                                               $ CASL_Sign.OpType 
                                                   CASL_AS.Total
                                                   (folType arity)
                                                   sort
             in sigMapH syms sig 
                 $ csig {CASL_Sign.opMap = CASL_Sign.addMapSet funcs func}
  where Just kind = getSymbolKind sym sig
        Just arity = getSymbolArity sym sig

-- generating axioms for a translated signature
generateAxioms :: Sign -> [Named (CASL_AS.CASLFORMULA)]
generateAxioms sig = predAx ++ funcAx ++ sortAx
                     where sorts = Set.toList $ getSymbolsByKind sig SortKind
                           funcs = Set.toList $ getSymbolsByKind sig FuncKind
                           preds = Set.toList $ getSymbolsByKind sig PredKind
                           sortAx = generateSortAxioms sig sorts
                           funcAx = generateFuncAxioms sig funcs
                           predAx = generatePredAxioms sig preds

-- generating axioms for translated predicate symbols
generatePredAxioms :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]
generatePredAxioms sig ps = concatMap (generatePredAxiomsH sig) ps

generatePredAxiomsH :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generatePredAxiomsH sig p = 
   if (length argNames == 0) 
      then [] 
      else [makeNamed ("gen_pred_" ++ show p) formula]
   where Just argNames = getArgumentNames p sig
         Just argTypes = getArgumentTypes p sig
         args = map makeVar argNames
         formula = makeForall 
                     argNames
                     (makeImplication 
                        (makeNegation (makeTypeHyps argTypes args sig))
                        (makeNegation (makePredication p args sig)))

-- generating axioms for translated function symbols
generateFuncAxioms :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]
generateFuncAxioms sig fs = concatMap (generateFuncAxiomsH sig) fs

generateFuncAxiomsH :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generateFuncAxiomsH sig f = 
   if (length argNames == 0) 
      then [makeNamed ("gen_func_1_" ++ show f) formula0]
      else [makeNamed ("gen_func_1_" ++ show f) formula1, 
            makeNamed ("gen_func_2_" ++ show f) formula2]
   where Just argNames = getArgumentNames f sig
         Just argTypes = getArgumentTypes f sig
         Just resultType = getReturnType f sig
         args = map makeVar argNames
         formula1 = makeForall 
                      argNames
                      (makeImplication  
                         (makeNegation (makeTypeHyps argTypes args sig))
                         (makeStrongEquation (makeApplication f args sig) bot))
         formula2 = makeForall 
                      argNames
                      (makeImplication 
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
   if (length argNames == 0) 
      then []
      else [makeNamed ("gen_sort_1_" ++ show s) formula]
   where Just argNames = getArgumentNames s sig
         Just argTypes = getArgumentTypes s sig
         args = map makeVar argNames
         elName = Token "gen_y" nr
         el = makeVar elName
         formula = makeForall 
                     argNames
                     (makeImplication 
                        (makeNegation (makeTypeHyps argTypes args sig))
                        (makeForall 
                           [elName]
                           (makeNegation 
                              (makePredication s (args ++ [el]) sig))))

generateSortAxiomsH2 :: Sign -> NAME -> [Named CASL_AS.CASLFORMULA]
generateSortAxiomsH2 sig s = 
   if (ar == 0)
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
                      (makeNegation (makePredication s (args1 ++ [bot]) sig))
         formula2 = makeForall 
                      (argNames1 ++ argNames2 ++ [elName])
                      (makeImplication 
                         (makeConjunction 
                            [makePredication s (args1 ++ [el]) sig, 
                             makePredication s (args2 ++ [el]) sig])
                         (makeConjunction 
                            $ map (\ (x,y) -> makeStrongEquation x y) 
                            $ zip args1 args2))
         formula0 = makeNegation (makePredication s [bot] sig)

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
                     (makeImplication 
                        (makeNegation (makeStrongEquation el bot))
                        (makeDisjunction $ map subformula ss))
         subformula s = if (ar s == 0)
                           then makePredication s [el] sig
                           else makeExists 
                                  (argNames s) 
                                  (makePredication s ((args s) ++ [el]) sig)
     
generateSortAxiomsH4 :: Sign -> [NAME] -> [Named CASL_AS.CASLFORMULA]          
generateSortAxiomsH4 sig ss = 
  map (generateSortAxiomsH4H sig) [ (s1,s2) | s1 <- ss, s2 <- ss, s1 < s2 ]

generateSortAxiomsH4H :: Sign -> (NAME, NAME) -> Named CASL_AS.CASLFORMULA
generateSortAxiomsH4H sig (s1,s2) = 
   makeNamed ("gen_sort_5_" ++ show s1 ++ "_" ++ show s2) formula
   where Just ar1 = getSymbolArity s1 sig
         Just ar2 = getSymbolArity s2 sig
         argNames1 = makeArgNames "x" ar1
         argNames2 = makeArgNames "y" ar2
         elName = Token "z" nr
         args1 = map makeVar argNames1
         args2 = map makeVar argNames2
         el = makeVar elName
         formula = makeForall 
                     (argNames1 ++ argNames2 ++ [elName])
                     (makeImplication 
                        (makePredication s1 (args1 ++ [el]) sig)
                        (makeNegation (makePredication s2 (args2 ++ [el]) sig)))
-- make argument names
makeArgNames :: String -> Int -> [NAME]
makeArgNames var n = map (\ i -> Token (var ++ "_" ++ show i) nr) [1..n]

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
  where Just kind = getSymbolKind
        Just arity = getSymbolArity p sig
        arity1 = if (kind == SortKind) then arity+1 else arity

-- make a strong equation
makeStrongEquation :: CASL_AS.CASLTERM -> CASL_AS.CASLTERM 
                      -> CASL_AS.CASLFORMULA
makeStrongEquation t1 t2 = CASL_AS.Strong_equation t1 t2 nr
 
-- make a negation
makeNegation :: CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA
makeNegation f = CASL_AS.Negation f nr
 
-- make a conjunction
makeConjunction :: [CASL_AS.CASLFORMULA] -> CASL_AS.CASLFORMULA
makeConjunction fs = CASL_AS.Conjunction fs nr

-- make a disjunction
makeDisjunction :: [CASL_AS.CASLFORMULA] -> CASL_AS.CASLFORMULA
makeDisjunction fs = CASL_AS.Disjunction fs nr

-- make an implication
makeImplication :: CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA 
                   -> CASL_AS.CASLFORMULA
makeImplication f g = CASL_AS.Implication f g True nr

-- make an equivalence
makeEquivalence :: CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA 
                   -> CASL_AS.CASLFORMULA
makeEquivalence f g = CASL_AS.Equivalence f g nr

-- make a universal quantification
makeForall :: [NAME] -> CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA
makeForall vars f = 
  CASL_AS.Quantification 
    CASL_AS.Universal [CASL_AS.Var_decl vars sort nr] f nr

-- make an existential quantification
makeExists :: [NAME] -> CASL_AS.CASLFORMULA -> CASL_AS.CASLFORMULA
makeExists vars f = 
  CASL_AS.Quantification 
    CASL_AS.Existential [CASL_AS.Var_decl vars sort nr] f nr 

-- make a type hypothesis
makeTypeHyp :: TYPE -> CASL_AS.CASLTERM -> Sign -> CASL_AS.CASLFORMULA
makeTypeHyp t term sig = makePredication s (args ++ [term]) sig
                         where Univ sortterm = t
                               (s,as) = termCanForm sortterm
                               args = map (termTransl sig) as

-- make type hypotheses
makeTypeHyps :: [TYPE] -> [CASL_AS.CASLTERM] 
                -> Sign -> CASL_AS.CASLFORMULA
makeTypeHyps ts terms sig = 
  makeConjunction $ map (\ (t, term) -> makeTypeHyp t term sig) $ zip ts terms

-- term translation
termTransl :: Sign -> TERM -> CASL_AS.CASLTERM
termTransl sig (Identifier x) = if not(isConstant x sig)
                                   then CASL_AS.Qual_var x sort nr
                                else makeApplication x [] sig
termTransl sig t = makeApplication f (map (termTransl sig) as) sig
                   where (f,as) = termCanForm t

-- signature translation
sigTransl :: Sign -> (CASL_Sign.CASLSign, [Named CASL_AS.CASLFORMULA]) 
sigTransl sig = (sigMap sig, generateAxioms sig)

-- theory translation
theoryTransl :: (Sign, [Named FORMULA]) -> 
                (CASL_Sign.CASLSign, [Named CASL_AS.CASLFORMULA])
theoryTransl (sig,fs) = (sigCASL, axCASL ++ fsCASL)
                        where (sigCASL, axCASL) = sigTransl sig
                              fsCASL = map (namedSenTransl sig) fs    

-- morphism translation
morphTransl :: Morphism -> CASL_Morphism.CASLMor
morphTransl (Morphism sig) = CASL_Morphism.idMor () $ sigMap sig 

-- sentence translation
senTransl :: Sign -> FORMULA -> CASL_AS.CASLFORMULA
senTransl _ T = CASL_AS.True_atom nr
senTransl _ F = CASL_AS.False_atom nr
senTransl sig (Pred t) = makePredication p (map (termTransl sig) as) sig
                         where (p,as) = termCanForm t
senTransl sig (Equality t1 t2) = 
  makeStrongEquation (termTransl sig t1) (termTransl sig t2)
senTransl sig (Negation f) = makeNegation (senTransl sig f)
senTransl sig (Conjunction fs) = makeConjunction (map (senTransl sig) fs)
senTransl sig (Disjunction fs) = makeDisjunction (map (senTransl sig) fs)
senTransl sig (Implication f g) = 
  makeImplication (senTransl sig f) (senTransl sig g)
senTransl sig (Equivalence f g) = 
  makeEquivalence (senTransl sig f) (senTransl sig g)
senTransl sig (Forall ds f) = 
  makeForall varNames 
             (makeImplication (makeTypeHyps types vars sig) (senTransl sig f))      
  where varNames = getVarsFromDecls ds
        vars = map makeVar varNames
        types = concatMap (\ (ns,t1) -> take (length ns) $ repeat t1) ds
senTransl sig (Exists ds f) = 
  makeExists varNames 
             (makeConjunction [makeTypeHyps types vars sig, senTransl sig f])      
  where varNames = getVarsFromDecls ds
        vars = map makeVar varNames 
        types = concatMap (\ (ns,t1) -> take (length ns) $ repeat t1) ds

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
                         $ CASL_Sign.OpType CASL_AS.Total (folType arity) sort
           SortKind -> CASL_Sign.PredAsItemType 
                         $ CASL_Sign.PredType (folType (arity+1))
  where n = name sym
        Just kind = getSymbolKind n sig
        Just arity = getSymbolArity n sig 

-- creates a Result
wrapInResult :: a -> Result a
wrapInResult x = Result [] $ Just x
