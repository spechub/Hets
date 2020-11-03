{- |
Module      :  ./Static/FromXmlUtils.hs
Description :  theory datastructure for development graphs
Copyright   :  (c) Christian Maeder, Simon Ulbricht, Uni Bremen 20011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

theory datastructure for development graphs
-}
module Static.FromXmlUtils where

import Static.GTheory

import Logic.Prover
import Logic.Logic
import Logic.Grothendieck

import Common.AnnoState
import Common.Doc
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Parsec
import Common.Result
import Common.Utils

import Text.ParserCombinators.Parsec

import qualified Data.Set as Set
import qualified Data.HashMap.Strict as Map

data BasicExtResponse = Failure Bool  -- True means fatal (give up)
  | Success G_theory Int (Set.Set G_symbol) Bool

extendByBasicSpec :: GlobalAnnos -> String -> G_theory
  -> (BasicExtResponse, String)
extendByBasicSpec ga str
  gt@(G_theory lid syn eSig@(ExtSign sign syms) si sens _)
  = let tstr = trimLeft str in
  if null tstr then (Success gt 0 Set.empty True, "") else
  case basicSpecParser Nothing lid of
    Nothing -> (Failure True, "missing basic spec parser")
    Just p -> case basic_analysis lid of
      Nothing -> (Failure True, "missing basic analysis")
      Just f -> case runParser (p Map.empty << eof) (emptyAnnos ()) "" tstr of
        Left err -> (Failure False, show err)
        Right bs -> let
          Result ds res = f (bs, sign, ga)
          in case res of
            Just (_, ExtSign sign2 syms2, sens2) | not (hasErrors ds) ->
              let sameSig = sign2 == sign
                  finExtSign = ExtSign sign2 $ Set.union syms syms2
              in
              (Success (G_theory lid syn (if sameSig then eSig else finExtSign)
                      (if sameSig then si else startSigId)
                      (joinSens (toThSens sens2) sens) startThId)
                      (length sens2)
                      (Set.map (G_symbol lid) $ Set.difference syms2 syms)
                      sameSig
              , if sameSig then
                   if null sens2 then "" else
                            show (vcat $ map (print_named lid) sens2)
                       else "")
            _ -> (Failure False, showRelDiags 1 ds)

deleteHiddenSymbols :: String -> G_sign -> Result G_sign
deleteHiddenSymbols syms gs@(G_sign lid (ExtSign sig _) _) = let
  str = trimLeft syms in if null str then return gs else
    case parse_symb_items lid of
      Nothing -> fail $ "no symbol parser for " ++ language_name lid
      Just sbpa -> case runParser (sepBy1 sbpa anComma << eof)
                   (emptyAnnos ()) "" str of
        Left err -> fail $ show err
        Right sms -> do
          rm <- stat_symb_items lid sig sms
          let sym1 = symset_of lid sig
              sym2 = Set.filter (\ s -> any (matches lid s) rm) sym1
          sig2 <- fmap dom $ cogenerated_sign lid sym2 sig
          return $ G_sign lid (mkExtSign sig2) startSigId

-- | reconstruct the morphism from symbols maps
getMorphism :: G_sign
  -> String -- ^ the symbol mappings
  -> Result G_morphism
getMorphism (G_sign lid (ExtSign sig _) _) syms =
    let str = trimLeft syms in
    if null str then return $ mkG_morphism lid $ ide sig else
    case parse_symb_map_items lid of
      Nothing -> fail $ "no symbol map parser for " ++ language_name lid
      Just smpa -> case runParser (sepBy1 smpa anComma << eof)
                   (emptyAnnos ()) "" str of
        Left err -> fail $ show err
        Right sms -> do
          rm <- stat_symb_map_items lid sig Nothing sms
          fmap (mkG_morphism lid) $ induced_from_morphism lid rm sig

-- | get the gmorphism for a gmorphism name
translateByGName :: LogicGraph -> G_sign
  -> String -- ^ the name of the morphism
  -> Result GMorphism
translateByGName lg gsig gname =
  let str = trim gname in
  if null str then ginclusion lg gsig gsig else do
    cmor <- lookupComorphism str lg
    gEmbedComorphism cmor gsig

-- | get the gmorphism for a gmorphism name with symbols maps
getGMorphism :: LogicGraph -> G_sign
  -> String -- ^ the name of the gmorphism
  -> String -- ^ the symbol mappings
  -> Result GMorphism
getGMorphism lg gsig gname syms = do
  gmor1 <- translateByGName lg gsig gname
  gmor2 <- fmap gEmbed $ getMorphism (cod gmor1) syms
  composeMorphisms gmor1 gmor2
