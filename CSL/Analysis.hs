{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}

-- todo: add static analysis for repeat

module CSL.Analysis
    ( splitSpec
    , basicCSLAnalysis
-- basicCSLAnalysis
-- ,mkStatSymbItems
-- ,mkStatSymbMapItem
-- ,inducedFromMorphism
-- ,inducedFromToMorphism
-- , signatureColimit
    )
    where

import Common.ExtSign
import Common.AS_Annotation
import Common.Id
import Common.Result
import Common.Utils (mapAccumLM)

import Control.Monad (unless)

import qualified Data.Set as Set
import Data.List
import Data.Maybe
import CSL.AS_BASIC_CSL
import CSL.Symbol
import CSL.Fold
import CSL.Sign as Sign


-- * Diagnosis Types and Functions


-- | extracts the operators, arity and extparam-count information
-- for an operator
extractOperatorsFromCmd :: CMD -> [(String, Int, Int)]
extractOperatorsFromCmd cmd =
    foldCMD r () cmd where
        r = (constRecord [] [])
            { foldAss = \ _ _ c def -> c ++ def
            , foldCmd = \ _ _ cmd' exps ->
                        (cmd', length exps, 0) : concat exps
            , foldRepeat = \ _ _ c l -> concat $ c:l
            , foldCond = \ _ _ l -> concat $ concatMap (uncurry (:)) l
            , foldSequence = \ _ _ l -> concat l

            , foldOp = \ _ _ s epl exps _ ->
                       (s, length exps, length epl) : concat exps
            , foldList = \ _ _ l _ -> concat l
            }

-- | checks whether the operator is correctly used which means that
-- for a predefined operator the following must hold:
-- (1) the actual arity must match the signature arity
-- (2) no extended params allowed
checkOperator :: (String, Int, Int)
               -> Maybe String -- ^ Points to the actual problem if any
checkOperator (op, arit, epc) =
    let err s = "At operator " ++ op ++ "\n" ++ s
        g s | epc > 0 = Just $ err s
                        ++ "* No extended parameters allowed\n"
            | null s = Nothing
            | otherwise = Just $ err s
    in case lookupOpInfo op arit of
         Left False -> Nothing
         -- if registered it must be registered with the given arity or
         -- as flex-op, otherwise we don't accept it
         Left True -> g "* Wrong arity\n"
         _ -> g ""

-- | generates a named formula
withName :: Annoted CMD -> Int -> Named CMD
withName f i = (makeNamed (if label == "" then "Ax_" ++ show i
                                   else label) $ item f)
               { isAxiom = not isTheorem }
    where
      label = getRLabel f
      annos = r_annos f
      isImplies' = foldl (\ y x -> isImplies x || y) False annos
      isImplied' = foldl (\ y x -> isImplied x || y) False annos
      isTheorem = isImplies' || isImplied'


-- | takes a signature and a formula and a number. 
-- It analyzes the formula and returns a formula with diagnosis
analyzeFormula :: Sign.Sign -> (Annoted CMD) -> Int -> Result (Named CMD)
analyzeFormula _ f i =
    do 
      let cmd = item f
          x = concat $ mapMaybe checkOperator $ extractOperatorsFromCmd cmd
      unless (null x) $ mkError x cmd
      return $ withName f{ item = staticUpdate cmd } i

-- | Extracts the axioms and the signature of a basic spec
splitSpec :: BASIC_SPEC -> Sign.Sign -> Result (Sign.Sign, [Named CMD])
splitSpec (Basic_spec specitems) sig =
    do
      ((newsig, _), mNCmds) <- mapAccumLM anaBasicItem (sig, 0) specitems
      return (newsig, catMaybes mNCmds)

anaBasicItem :: (Sign.Sign, Int) -> Annoted BASIC_ITEM
             -> Result ((Sign.Sign, Int), Maybe (Named CMD))
anaBasicItem acc@(sign, i) itm =
    case item itm of
      Op_decl (Op_item tokens _) -> return ((addTokens sign tokens, i), Nothing)
      Var_decls _ -> return (acc, Nothing) -- TODO: implement
      Axiom_item annocmd ->
          do
            ncmd <- analyzeFormula sign annocmd i
            return ((sign, i+1), Just ncmd)

-- | adds the specified tokens to the signature
addTokens :: Sign.Sign -> [Token] -> Sign.Sign
addTokens sign tokens = let f res itm = addToSig res $ simpleIdToId itm
                        in foldl f sign tokens


-- | stepwise extends an initially empty signature by the basic spec
-- bs. The resulting spec contains analyzed axioms in it. The result
-- contains: (1) the basic spec (2) the new signature + the added
-- symbols (3) sentences of the spec
basicCSLAnalysis :: (BASIC_SPEC, Sign, a)
                 -> Result (BASIC_SPEC, ExtSign Sign Symbol, [Named CMD])
basicCSLAnalysis (bs, sig, _) =
    do 
      (newSig, ncmds) <- splitSpec bs sig
      let newSyms = Set.map Symbol $ Set.difference (items newSig) $ items sig
      return (bs, ExtSign newSig newSyms, ncmds)

-- | A function which regroups all updates on a CMD during the static analysis.
staticUpdate :: CMD -> CMD
staticUpdate = handleFunAssignment

-- | Replaces the function-arguments in functional assignments by variables
-- instead of operators.
handleFunAssignment :: CMD -> CMD
handleFunAssignment (Ass (Op f epl al@(_:_) rg) e) =
   let opToVar' s (Op v _ _ rg') =
           (Set.insert v s, Var Token{ tokStr = v, tokPos = rg' })
       opToVar' _ x =
           error $ "handleFunAssignment: not supported varexpression " ++ show x
       (env, al') = mapAccumL opToVar' Set.empty al
   in Ass (Op f epl al' rg) $ constsToVars env e

handleFunAssignment x = x

constsToVars :: Set.Set String -> EXPRESSION -> EXPRESSION
constsToVars env e =
    let substRec =
            idRecord
            { foldOp =
                  \ env' _ s epl' args rg' ->
                      if Set.member s env' then
                          if null args
                          then Var (Token { tokStr = s, tokPos = rg' })
                          else error $ "constsToVars: variable must not have"
                                   ++ " arguments:" ++ show args
                      else Op s epl' args rg'
            , foldList = \ _ _ l rg' -> List l rg'
            }
    in foldTerm substRec env e
