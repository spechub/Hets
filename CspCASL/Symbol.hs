{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./CspCASL/Symbol.hs
Description :  semantic csp-casl symbols
Copyright   :  (c) Christian Maeder, DFKI GmbH 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CspCASL.Symbol where

import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.SignCSP
import CspCASL.SymbItems

import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sign

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result
import qualified Common.Lib.MapSet as MapSet

import Data.Data
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad
import qualified Control.Monad.Fail as Fail

data CspSymbType
  = CaslSymbType SymbType
  | ProcAsItemType ProcProfile
  | ChanAsItemType Id -- the SORT
  deriving (Show, Eq, Ord, Typeable, Data)

instance Pretty CspSymbType where
 pretty (CaslSymbType st)  = pretty $ symbolKind st
 pretty (ProcAsItemType _) = text "process"
 pretty (ChanAsItemType _) = text "channel"

data CspSymbol = CspSymbol {cspSymName :: Id, cspSymbType :: CspSymbType}
  deriving (Show, Eq, Ord, Typeable, Data)

data CspRawSymbol = ACspSymbol CspSymbol | CspKindedSymb CspSymbKind Id
  deriving (Show, Eq, Ord, Typeable, Data)

rawId :: CspRawSymbol -> Id
rawId r = case r of
  ACspSymbol s -> cspSymName s
  CspKindedSymb _ i -> i

instance Pretty CspSymbol where
  pretty (CspSymbol i t) = case t of
    ProcAsItemType p -> keyword processS <+> pretty i <+> pretty p
    ChanAsItemType s -> keyword channelS <+> pretty i <+> colon <+> pretty s
    CaslSymbType c -> pretty $ Symbol i c

instance GetRange CspSymbol where
  getRange (CspSymbol i _) = getRange i

instance Pretty CspRawSymbol where
  pretty r = case r of
    ACspSymbol s -> pretty s
    CspKindedSymb k i -> pretty k <+> pretty i

instance GetRange CspRawSymbol where
  getRange r = case r of
    ACspSymbol s -> getRange s
    CspKindedSymb _ i -> getRange i

cspCheckSymbList :: [CspSymbMap] -> [Diagnosis]
cspCheckSymbList l = case l of
  CspSymbMap (CspSymb a Nothing) Nothing
    : CspSymbMap (CspSymb b (Just t)) _ : r -> mkDiag Warning
           ("profile '" ++ showDoc t "' does not apply to '"
            ++ showId a "' but only to") b : cspCheckSymbList r
  _ : r -> cspCheckSymbList r
  [] -> []

toChanSymbol :: (CHANNEL_NAME, SORT) -> CspSymbol
toChanSymbol (c, s) = CspSymbol c $ ChanAsItemType s

toProcSymbol :: (PROCESS_NAME, ProcProfile) -> CspSymbol
toProcSymbol (n, p) = CspSymbol n $ ProcAsItemType p

idToCspRaw :: Id -> CspRawSymbol
idToCspRaw = CspKindedSymb $ CaslKind Implicit

sortToProcProfile :: SORT -> ProcProfile
sortToProcProfile = ProcProfile [] . Set.singleton . CommTypeSort

cspTypedSymbKindToRaw :: Bool -> CspCASLSign -> CspSymbKind -> Id -> CspType
  -> Result CspRawSymbol
cspTypedSymbKindToRaw b sig k idt t = let
    csig = extendedInfo sig
    getSet = MapSet.lookup idt
    chs = getSet $ chans csig
    prs = getSet $ procSet csig
    reduce = reduceProcProfile $ sortRel sig
    err = plain_error (idToCspRaw idt)
              (showDoc idt " " ++ showDoc t
               " does not have kind " ++ showDoc k "") nullRange
    in case k of
     ProcessKind -> case t of
       ProcType p -> return $ ACspSymbol $ toProcSymbol (idt, reduce p)
       CaslType (A_type s) -> return
         $ ACspSymbol $ toProcSymbol
             (idt, reduce $ sortToProcProfile s)
       _ -> err
     ChannelKind -> case t of
       CaslType (A_type s) ->
         return $ ACspSymbol $ toChanSymbol (idt, s)
       _ -> err
     CaslKind ck -> case t of
       CaslType ct -> let
         caslAnno = fmap (\ r -> case r of
           ASymbol sy -> ACspSymbol $ CspSymbol idt $ CaslSymbType $ symbType sy
           _ -> CspKindedSymb k idt) $ typedSymbKindToRaw b sig ck idt ct
         in case ct of
         A_type s | b && ck == Implicit ->
           let hasChan = Set.member s chs
               cprs = Set.filter (\ (ProcProfile args al) ->
                 null args && any (\ cs -> case cs of
                            CommTypeSort r -> r == s
                              || Set.member s (subsortsOf r sig)
                            CommTypeChan (TypedChanName c _) ->
                              c == s) (Set.toList al)) prs
           in case Set.toList cprs of
             [] -> if hasChan then do
                 appendDiags [mkDiag Hint "matched channel" idt]
                 return $ ACspSymbol $ toChanSymbol (idt, s)
               else caslAnno
             pr : rpr -> do
               when (hasChan || not (null rpr)) $
                 appendDiags [mkDiag Warning "ambiguous matches" idt]
               appendDiags [mkDiag Hint "matched process" idt]
               return $ ACspSymbol $ toProcSymbol (idt, pr)
         _ -> caslAnno
       ProcType p | ck == Implicit ->
         return $ ACspSymbol $ toProcSymbol (idt, reduce p)
       _ -> err

cspSymbToRaw :: Bool -> CspCASLSign -> CspSymbKind -> CspSymb
  -> Result CspRawSymbol
cspSymbToRaw b sig k (CspSymb idt mt) = case mt of
  Nothing -> return $ case k of
    CaslKind Sorts_kind ->
      ACspSymbol $ CspSymbol idt $ CaslSymbType SortAsItemType
    _ -> CspKindedSymb k idt
  Just t -> cspTypedSymbKindToRaw b sig k idt t

cspStatSymbItems :: CspCASLSign -> [CspSymbItems] -> Result [CspRawSymbol]
cspStatSymbItems sig sl =
  let st (CspSymbItems kind l) = do
        appendDiags $ cspCheckSymbList $ map (`CspSymbMap` Nothing) l
        mapM (cspSymbToRaw True sig kind) l
  in fmap concat (mapM st sl)

maxKind :: CspSymbKind -> CspRawSymbol -> CspSymbKind
maxKind k rs = case k of
  CaslKind Implicit -> case rs of
    ACspSymbol (CspSymbol _ ty) -> case ty of
      ProcAsItemType _ -> ProcessKind
      ChanAsItemType _ -> ChannelKind
      CaslSymbType cTy -> case cTy of
        OpAsItemType _ -> CaslKind Ops_kind
        PredAsItemType _ -> CaslKind Preds_kind
        _ -> CaslKind Sorts_kind
    _ -> k
  _ -> k

cspSymbOrMapToRaw :: CspCASLSign -> Maybe CspCASLSign -> CspSymbKind
  -> CspSymbMap -> Result [(CspRawSymbol, CspRawSymbol)]
cspSymbOrMapToRaw sig msig k (CspSymbMap s mt) = case mt of
  Nothing -> do
      v <- cspSymbToRaw True sig k s
      return [(v, v)]
  Just t -> do
      appendDiags $ case (s, t) of
        (CspSymb a Nothing, CspSymb b Nothing) | a == b ->
          [mkDiag Hint "unneeded identical mapping of" a]
        _ -> []
      w <- cspSymbToRaw True sig k s
      let nk = maxKind k w
      x <- case msig of
             Nothing -> cspSymbToRaw False sig nk t
             Just tsig -> cspSymbToRaw True tsig nk t
      let mkS i = ACspSymbol $ CspSymbol i $ CaslSymbType SortAsItemType
          pairS s1 s2 = (mkS s1, mkS s2)
      case (w, x) of
        (ACspSymbol c1@(CspSymbol _ t1), ACspSymbol c2@(CspSymbol _ t2)) ->
          case (t1, t2) of
            (ChanAsItemType s1, ChanAsItemType s2) ->
              return [(w, x), (mkS s1, mkS s2)]
            (ProcAsItemType (ProcProfile args1 _),
             ProcAsItemType (ProcProfile args2 _))
              | length args1 == length args2 ->
              return $ (w, x)
                : zipWith pairS args1 args2
            (CaslSymbType (PredAsItemType (PredType args1)),
             CaslSymbType (PredAsItemType (PredType args2)))
              | length args1 == length args2 ->
              return $ (w, x)
                : zipWith pairS args1 args2
            (CaslSymbType (OpAsItemType (OpType _ args1 res1)),
             CaslSymbType (OpAsItemType (OpType _ args2 res2)))
              | length args1 == length args2 ->
              return $ (w, x)
                : zipWith pairS (res1 : args1) (res2 : args2)
            (CaslSymbType SortAsItemType, CaslSymbType SortAsItemType) ->
              return [(w, x)]
            _ -> Fail.fail $ "profiles of '" ++ showDoc c1 "' and '"
               ++ showDoc c2 "' do not match"
        _ -> return [(w, x)]

cspStatSymbMapItems :: CspCASLSign -> Maybe CspCASLSign -> [CspSymbMapItems]
  -> Result (Map.Map CspRawSymbol CspRawSymbol)
cspStatSymbMapItems sig msig sl = do
  let st (CspSymbMapItems kind l) = do
        appendDiags $ cspCheckSymbList l
        fmap concat $ mapM (cspSymbOrMapToRaw sig msig kind) l
      getSort rsy = case rsy of
        ACspSymbol (CspSymbol i (CaslSymbType SortAsItemType)) -> Just i
        _ -> Nothing
      getImplicit rsy = case rsy of
        CspKindedSymb (CaslKind Implicit) i -> Just i
        _ -> Nothing
      mkSort i = ACspSymbol $ CspSymbol i $ CaslSymbType SortAsItemType
      mkImplicit = idToCspRaw
  ls <- mapM st sl
  foldM (insertRsys rawId getSort mkSort getImplicit mkImplicit)
                    Map.empty (concat ls)

toSymbolSet :: CspSign -> [Set.Set CspSymbol]
toSymbolSet csig = map Set.fromList
  [ map toChanSymbol $ mapSetToList $ chans csig
  , map toProcSymbol $ mapSetToList $ procSet csig ]

symSets :: CspCASLSign -> [Set.Set CspSymbol]
symSets sig = map (Set.map caslToCspSymbol) (symOf sig)
  ++ toSymbolSet (extendedInfo sig)

caslToCspSymbol :: Symbol -> CspSymbol
caslToCspSymbol sy = CspSymbol (symName sy) $ CaslSymbType $ symbType sy

-- | try to convert a csp raw symbol to a CASL raw symbol
toRawSymbol :: CspRawSymbol -> Maybe RawSymbol
toRawSymbol r = case r of
  ACspSymbol (CspSymbol i (CaslSymbType t)) -> Just (ASymbol $ Symbol i t)
  CspKindedSymb (CaslKind k) i -> Just (AKindedSymb k i)
  _ -> Nothing

splitSymbolMap :: Map.Map CspRawSymbol CspRawSymbol
  -> (RawSymbolMap, Map.Map CspRawSymbol CspRawSymbol)
splitSymbolMap = Map.foldrWithKey (\ s t (cm, ccm) ->
  case (toRawSymbol s, toRawSymbol t) of
    (Just c, Just d) -> (Map.insert c d cm, ccm)
    _ -> (cm, Map.insert s t ccm)) (Map.empty, Map.empty)

getCASLSymbols :: Set.Set CspSymbol -> Set.Set Symbol
getCASLSymbols = Set.fold (\ (CspSymbol i ty) -> case ty of
    CaslSymbType t -> Set.insert $ Symbol i t
    _ -> id) Set.empty
