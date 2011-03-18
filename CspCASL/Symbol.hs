{- |
Module      :  $Header$
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
import CspCASL.SymbItems

import CASL.AS_Basic_CASL
import CASL.Morphism
import CASL.Sign

import Common.Doc
import Common.DocUtils
import Common.Id
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad

data CspSymbType
  = CaslSymbType SymbType
  | ProcAsItemType ProcProfile
  | ChanAsItemType Id -- the SORT
  deriving (Show, Eq, Ord)

data CspSymbol = CspSymbol {cspSymName :: Id, cspSymbType :: CspSymbType}
  deriving (Show, Eq, Ord)

data CspRawSymbol = ACspSymbol CspSymbol | CspKindedSymb SymbKind Id
  deriving (Show, Eq, Ord)

rawId :: CspRawSymbol -> Id
rawId r = case r of
  ACspSymbol s -> cspSymName s
  CspKindedSymb _ i -> i

instance Pretty CspSymbType where
  pretty t = case t of
    CaslSymbType c -> pretty c
    ProcAsItemType p -> pretty p
    ChanAsItemType s -> pretty s

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

cspCheckSymbList :: [SymbMap] -> [Diagnosis]
cspCheckSymbList l = case l of
  SymbMap (CspSymb a Nothing) Nothing
    : SymbMap (CspSymb b (Just t)) _ : r -> mkDiag Warning
           ("profile '" ++ showDoc t "' does not apply to '"
            ++ showId a "' but only to") b : cspCheckSymbList r
  _ : r -> cspCheckSymbList r
  [] -> []

cspTypedSymbKindToRaw :: SymbKind -> Id -> CspType -> Result CspRawSymbol
cspTypedSymbKindToRaw k idt t = let
    err = plain_error (CspKindedSymb (CaslKind Implicit) idt)
              (showDoc idt " " ++ showDoc t
               " does not have kind " ++ showDoc k "") nullRange
    in case k of
     ProcessKind -> case t of
       ProcType p -> return $ ACspSymbol $ CspSymbol idt $ ProcAsItemType p
       CaslType (A_type s) -> return
         $ ACspSymbol $ CspSymbol idt $ ProcAsItemType $
           ProcProfile [] $ Set.singleton $ CommTypeSort s
       _ -> err
     ChannelKind -> case t of
       CaslType (A_type s) ->
         return $ ACspSymbol $ CspSymbol idt $ ChanAsItemType s
       _ -> err
     CaslKind ck -> case t of
       CaslType ct -> fmap (\ r -> case r of
         ASymbol sy -> ACspSymbol $ CspSymbol idt $ CaslSymbType $ symbType sy
         _ -> CspKindedSymb k idt)
         $ typedSymbKindToRaw ck idt ct
       _ -> err

cspSymbToRaw :: SymbKind -> Symb -> Result CspRawSymbol
cspSymbToRaw k (CspSymb idt mt) = case mt of
  Nothing -> return $ case k of
    CaslKind Sorts_kind ->
      ACspSymbol $ CspSymbol idt $ CaslSymbType SortAsItemType
    _ -> CspKindedSymb k idt
  Just t -> cspTypedSymbKindToRaw k idt t

cspStatSymbItems :: [SymbItems] -> Result [CspRawSymbol]
cspStatSymbItems sl =
  let st (SymbItems kind l) = do
        appendDiags $ cspCheckSymbList $ map (`SymbMap` Nothing) l
        mapM (cspSymbToRaw kind) l
  in fmap concat (mapM st sl)

cspSymbOrMapToRaw :: SymbKind -> SymbMap
   -> Result [(CspRawSymbol, CspRawSymbol)]
cspSymbOrMapToRaw k (SymbMap s mt) = case mt of
  Nothing -> do
      v <- cspSymbToRaw k s
      return [(v, v)]
  Just t -> do
      appendDiags $ case (s, t) of
        (CspSymb a Nothing, CspSymb b Nothing) | a == b ->
          [mkDiag Hint "unneeded identical mapping of" a]
        _ -> []
      w <- cspSymbToRaw k s
      x <- cspSymbToRaw k t
      let mkS i = ACspSymbol $ CspSymbol i $ CaslSymbType SortAsItemType
          pairS s1 s2 = (mkS s1, mkS s2)
      case (w, x) of
        (ACspSymbol (CspSymbol _ t1), ACspSymbol (CspSymbol _ t2)) ->
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
            _ -> fail $ "profiles '" ++ showDoc t1 "' and '"
               ++ showDoc t2 "' do not match"
        _ -> return [(w, x)]

cspStatSymbMapItems :: [SymbMapItems]
  -> Result (Map.Map CspRawSymbol CspRawSymbol)
cspStatSymbMapItems sl = do
  let st (SymbMapItems kind l) = do
        appendDiags $ cspCheckSymbList l
        fmap concat $ mapM (cspSymbOrMapToRaw kind) l
      getSort rsy = case rsy of
        ACspSymbol (CspSymbol i (CaslSymbType SortAsItemType)) -> Just i
        _ -> Nothing
      getImplicit rsy = case rsy of
        CspKindedSymb (CaslKind Implicit) i -> Just i
        _ -> Nothing
      mkSort i = ACspSymbol $ CspSymbol i $ CaslSymbType SortAsItemType
      mkImplicit = CspKindedSymb $ CaslKind Implicit
  ls <- mapM st sl
  foldM (insertRsys rawId getSort mkSort getImplicit mkImplicit)
                    Map.empty (concat ls)
