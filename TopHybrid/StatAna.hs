{-# LANGUAGE ExistentialQuantification, OverloadedStrings #-}
{- |
Module      :  ./TopHybrid/StatAna.hs
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  nevrenato@gmail.com
Stability   :  experimental
Portability :  not portable

Description :
Static analysis of hybrid logic with an arbitrary logic below.
-}

module TopHybrid.StatAna (thAna, anaForm', simSen) where

import Logic.Logic
import TopHybrid.AS_TopHybrid
import TopHybrid.TopHybridSign
import TopHybrid.Print_AS ()
import TopHybrid.Utilities
import TopHybrid.ATC_TopHybrid ()
import CASL.Sign -- Symbols, this should be removed...
import Common.GlobalAnnotations
import Common.Result
import Common.ExtSign
import Common.AS_Annotation
import Common.Id
import Common.DocUtils
import Control.Monad
import Data.List
import Data.Set
import Unsafe.Coerce
import ATerm.Lib
import Data.Aeson(FromJSON, ToJSON, parseJSON, toJSON, object, (.=), Value(Null))

bimap :: (t1 -> t2) -> (s1 -> s2) -> (t1, s1) -> (t2, s2)
bimap f g (a, b) = (f a, g b)

-- | Collects the newly declared nomies and modies
colnomsMods :: [TH_BASIC_ITEM] -> ([MODALITY], [NOMINAL])
colnomsMods = Data.List.foldr f ([], [])
        where f (Simple_mod_decl ms) = bimap (++ ms) id
              f (Simple_nom_decl ns) = bimap id (++ ns)

{- | Adds the newly declared nomies/modies, and the analysed base
signature to a new sig
checking for redundancy of modalities and nominals declarations
Note : If there are repeated declarations, the size of the sets should
be differnt that the size of the lists -}
topAna :: (Logic l sub bs sen si smi sign mor symb raw pf) =>
                [TH_BASIC_ITEM] -> l -> sign -> Result Sgn_Wrap
topAna ds l sig = if not rep then return newSig else mkHint newSig msg
                where
                x = colnomsMods ds
                x' = bimap fromList fromList x
                rep = size (uncurry Data.Set.union x') /=
                      length (uncurry (++) x)
                s = uncurry THybridSign x' sig
                newSig = Sgn_Wrap l s
                msg = maybeE 0 Nothing

{- Checks if the modalities and nominals referred in a sentence, really exist
in the signature -}
nomOrModCheck :: (Pretty f, GetRange f) => Set SIMPLE_ID -> SIMPLE_ID ->
                                           TH_FORMULA f -> Result (TH_FORMULA f)
nomOrModCheck xs x = if member x xs then return else mkError msg
     where msg = maybeE 1 Nothing


{- | Top Formula analyser
The l argument could be discarded, but then we would need an extra unsafe
function, to convert the spec type...
As l corresponds to the underlying logic bs should correspond to the
underlying spec, as some formula analysers need the spec associated
with it -}
anaForm :: (Logic l sub bs sen si smi sign mor symb raw pf) =>
        l -> bs -> Sgn_Wrap -> Frm_Wrap -> Result Frm_Wrap
anaForm l bs s (Frm_Wrap _ f) = liftM (Frm_Wrap l) $ unroll l bs s f

{- Static analysis of an hybridized sentence, when it's called by an upper
level logic. (This is only used when we want to analyse 2 or more times
hybridized, sentences). Probably this function can be merged smoothly with
the above. I will check this later

An hybridized sentence, with the correpondent sign already built, doesn't
need the top spec, hence we can discard it and just use the underlying (und) -}
anaForm' :: (Spc_Wrap, Sgn_Wrap, Frm_Wrap) -> Result Frm_Wrap
anaForm' (Spc_Wrap l bs _, s, f) = anaForm l (und bs) s f

-- | Unrolling the formula, so that we can analyse it further
unroll :: (Show f, GetRange f, ShATermConvertible f,
             Logic l sub bs sen sy sm si mo sy' rs pf) =>
                l -> bs -> Sgn_Wrap -> TH_FORMULA f -> Result (TH_FORMULA sen)
unroll l bs s'@(Sgn_Wrap _ s) f =
        case f of
                  (At n f') -> liftM (At n) $ unroll l bs s' f' >>=
                                 nomOrModCheck (nomies s) n
                  (Box m f') -> liftM (Box m) $ unroll l bs s' f' >>=
                                 nomOrModCheck (modies s) m
                  (Dia m f') -> liftM (Dia m) $ unroll l bs s' f' >>=
                                 nomOrModCheck (modies s) m
                  (Conjunction f' f'') -> liftM2 Conjunction
                                           (unroll l bs s' f')
                                           (unroll l bs s' f'')
                  (Disjunction f' f'') -> liftM2 Disjunction
                                           (unroll l bs s' f')
                                           (unroll l bs s' f'')
                  (Implication f' f'') -> liftM2 Implication
                                           (unroll l bs s' f')
                                           (unroll l bs s' f'')
                  (BiImplication f' f'') -> liftM2 BiImplication
                                             (unroll l bs s' f')
                                             (unroll l bs s' f'')
                  (Here n) -> nomOrModCheck (nomies s) n $ Here n
                  (Neg f') -> liftM Neg (unroll l bs s' f')
                  (Uni n f') -> (liftM $ Uni n) (unroll l bs
                   (addNomToSig n s') f') >>= checkForRepNom n (nomies s)
                  (Exist n f') -> (liftM $ Exist n) (unroll l bs
                   (addNomToSig n s') f') >>= checkForRepNom n (nomies s)
                  (UnderLogic f') ->
                   liftM UnderLogic $ undFormAna l (extended s) f' bs
                  (Par f') -> liftM Par (unroll l bs s' f')
                  TrueA -> return TrueA
                  FalseA -> return FalseA
unroll _ _ EmptySign _ = error "Signature not computable"

-- helper function
addNomToSig :: NOMINAL -> Sgn_Wrap -> Sgn_Wrap
addNomToSig n (Sgn_Wrap l s) = Sgn_Wrap l s
 { nomies = Data.Set.insert n $ nomies s}
addNomToSig _ EmptySign = error "Signature not computable"

checkForRepNom :: (Pretty f, GetRange f) =>
        NOMINAL -> Set NOMINAL -> TH_FORMULA f -> Result (TH_FORMULA f)
checkForRepNom n s = if member n s
        then mkError "conflict in nominal decl and quantification"
        else return
{- | Lift of the formula analyser
Analyses each formula and collects the results. Converting also the
annotations to the correct format. The function flipM is needed because
we want the annotations independent from the analyser -}
anaForms :: (Logic l sub bs sen si smi sign mor symb raw pf) =>
        l -> bs -> [Annoted Frm_Wrap] -> Sgn_Wrap -> Result [Named Frm_Wrap]
anaForms l bs f s = mapM (flipM . makeNamedSen . fmap (anaForm l bs s)) f

-- Just flips the monad position with the functor
flipM :: (Monad m) => Named (m a) -> m (Named a)
flipM y = sentence y >>= \ a -> return $ mapNamed (const a) y

{- | Examining the list of formulas and collecting results

Analyses first the underlying spec; Then analyses the top spec
(without the axioms) and merges the resulting sig with the underlying one.
Also translates the underlying axioms into hybridized ones, so that in the
end all axioms are of the same type;
Next analyses the hybrid axioms and puts them together with the already
translated axioms.
Finnaly prepares the tuple format for outputting. -}
thAna :: (Spc_Wrap, Sgn_Wrap, GlobalAnnos) ->
        Result (Spc_Wrap, ExtSign Sgn_Wrap Symbol, [Named Frm_Wrap])
thAna (Spc_Wrap l sp fs, _, _) = finalRes
        where
        undA = undAna l $ und sp
        partMerge = undA >>= \ (x1, x2, x3) -> topAna (bitems sp) l
                     (plainSign x2) >>= \ x -> return (x1, x, formMap x3)
        partMerge' = partMerge >>= \ (x1, x2, x3) ->
                      anaForms l x1 fs x2 >>= \ x -> return (x1, x2, x3 ++ x)
        finalRes = partMerge' >>= \ (x1, x2, x3) ->
                    return (mergSpec x1, mkExtSign x2, x3)
        formMap = Data.List.map $ mapNamed $ Frm_Wrap l . UnderLogic
        mergSpec e = Spc_Wrap l (Bspec (bitems sp) e) fs


-- Analysis of the underlying logic spec
undAna :: (StaticAnalysis l bs sen si smi sign mor symb raw) =>
                l -> bs -> Result (bs, ExtSign sign symb, [Named sen])
undAna l b = (maybeE 2 $ basic_analysis l) x
        where x = (b, empty_signature l, emptyGlobalAnnos)

unsafeToForm :: (StaticAnalysis l bs sen si smi sign mor symb raw) =>
                l -> a -> sen
unsafeToForm _ = unsafeCoerce
unsafeToSig :: (StaticAnalysis l bs sen si smi sign mor symb raw) =>
               l -> a -> sign
unsafeToSig _ = unsafeCoerce

{- Analysis of the sentences part the corresponds to the underlying logic. We
   need to use the unsafe functions here, because the typechecker has no way
   to check the (simple) relations (l -> sig) and (l -> sen). In other words
   it can't check that the arguments l and a belong to the Logic class,
   likewise for l -> b. The unsafe functions will give the "right"
   type associated with l. -}
undFormAna :: (StaticAnalysis l bs sen si smi sign mor symb raw) =>
                l -> a -> b -> bs -> Result sen
undFormAna l a b c = (maybeE 4 $ sen_analysis l) (c, a', b')
        where a' = unsafeToSig l a
              b' = unsafeToForm l b


{- -- Operations on sentences ----
How can we guarantee that the l in Sgn_Wrap is equal
to the l in Frm_Wrap ? -}
simSen :: Sgn_Wrap -> Frm_Wrap -> Frm_Wrap
simSen (Sgn_Wrap _ s) (Frm_Wrap l f) = Frm_Wrap l $
                uroll l (unsafeCoerce (extended s)) f
simSen EmptySign _ = error "The signature cannot be empty"

uroll :: (Logic l sub bs f s sm sgn mo sy rw pf) =>
        l -> sgn -> TH_FORMULA f -> TH_FORMULA f
uroll l s f = case f of
                At n f' -> At n $ uroll l s f'
                Box m f' -> Box m $ uroll l s f'
                Dia m f' -> Dia m $ uroll l s f'
                Conjunction f' f'' -> Conjunction (uroll l s f') $ uroll l s f''
                Disjunction f' f'' -> Disjunction (uroll l s f') $ uroll l s f''
                Implication f' f'' -> Implication (uroll l s f') $ uroll l s f''
                BiImplication f' f'' -> BiImplication (uroll l s f') $
                                         uroll l s f''
                Here n -> Here n
                Neg f' -> Neg $ uroll l s f'
                Par f' -> Par $ uroll l s f'
                UnderLogic f' -> UnderLogic $ simplify_sen l s f'
                x -> x

{- These instances should be automatically generated by DriFT, but it cannot
since they are not declared in a usual format -}
instance ShATermConvertible Sgn_Wrap where
         toShATermAux att (Sgn_Wrap _ s) = toShATermAux att s
         toShATermAux _ EmptySign = error "I entered in emptySign"
         fromShATermAux _ _ = error "I entered here"

instance ShATermConvertible Spc_Wrap where
         toShATermAux att (Spc_Wrap _ s _) = toShATermAux att s
         fromShATermAux _ _ = error "I entered here"

instance ShATermConvertible Frm_Wrap where
        toShATermAux att (Frm_Wrap _ f) = toShATermAux att f
        fromShATermAux _ _ = error "I entered here"



instance ToJSON Sgn_Wrap where
  toJSON (Sgn_Wrap _ s) = toJSON s
  toJSON EmptySign = Null
instance FromJSON Sgn_Wrap where
  parseJSON = error "fromJSON not implemented for Sgn_Wrap"

instance ToJSON Spc_Wrap where
  toJSON (Spc_Wrap _ spec sen) = object ["spec" .= spec, "sen" .= sen]
instance FromJSON Spc_Wrap where
  parseJSON = error "fromJSON not implemented for Spc_Wrap"

instance ToJSON Frm_Wrap where
  toJSON (Frm_Wrap _ f) = toJSON f
instance FromJSON Frm_Wrap where
  parseJSON = error "fromJSON not implemented for Frm_Wrap"
