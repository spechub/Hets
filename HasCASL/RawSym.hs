{- |
Module      :  ./HasCASL/RawSym.hs
Description :  raw symbol functions
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

raw symbols bridge symb items and the symbols of a signature
-}

module HasCASL.RawSym where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.ClassAna
import HasCASL.Le
import HasCASL.Merge (addUnit)
import HasCASL.PrintLe (addClassMap)
import HasCASL.VarDecl

import Common.DocUtils
import Common.Id
import Common.Result
import Common.Lib.State
import qualified Data.Map as Map

statSymbMapItems :: Env -> [SymbMapItems] -> Result RawSymbolMap
statSymbMapItems e sl = do
    rs <- mapM ( \ (SymbMapItems kind l _ _)
                 -> mapM (symbOrMapToRaw e kind) l) sl
    foldr ( \ (r1, r2) mm -> do
            m <- mm
            if Map.member r1 m then do
                Result [Diag Error ("duplicate mapping for: " ++
                          showDoc r1 "\n ignoring: " ++ showDoc r2 "")
                       $ posOfId $ rawSymName r2] $ Just ()
                return m
              else return $ Map.insert r1 r2 m)
          (return Map.empty) $ concat rs

symbOrMapToRaw :: Env -> SymbKind -> SymbOrMap -> Result (RawSymbol, RawSymbol)
symbOrMapToRaw e k (SymbOrMap s mt _) = do
    s1 <- symbToRaw (Just e) k s
    s2 <- case mt of
      Nothing -> return s1
      Just t -> symbToRaw Nothing k t
    return (s1, s2)

statSymbItems :: Env -> [SymbItems] -> Result [RawSymbol]
statSymbItems e sl = do
  rs <- mapM (\ (SymbItems kind l _ _)
              -> mapM (symbToRaw (Just e) kind) l) sl
  return $ concat rs

symbToRaw :: Maybe Env -> SymbKind -> Symb -> Result RawSymbol
symbToRaw me k (Symb idt mt _) = case mt of
    Nothing -> return $ symbKindToRaw k idt
    Just (SymbType sc@(TypeScheme vs t _)) -> case me of
      Nothing ->
        hint (symbKindToRaw k idt) "ignoring target symbol qualification"
          $ getRange sc
      Just e ->
        let qi ty = ASymbol $ Symbol idt ty
            rsc = if k == SyKpred then predTypeScheme (posOfId idt) sc else sc
            r = do
              let cm = addClassMap cpoMap (classMap e)
                  (mtysc, rLe) = runState (anaTypeScheme rsc) e
                    { typeMap = addUnit cm $ typeMap e
                    , classMap = cm }
              case mtysc of
                Nothing -> Result (reverse
                  $ mkDiag Error "no function type" rsc : envDiags rLe) Nothing
                Just asc -> return $ qi $ OpAsItemType asc
            rk = if null vs then do
                (_, ck) <- convTypeToKind t
                maybeResult $ anaKindM ck $ classMap e
              else Nothing
        in case rk of
             Nothing -> case k of
               Implicit -> r
               SyKop -> r
               SyKpred -> r
               _ -> mkError "not a valid kind" t
             Just fk -> case k of
               Implicit -> -- check here which symbol is in the signature
                 case maybeResult r of
                 Just sy -> return sy
                 _ -> return $ qi $ TypeAsItemType fk
               SyKop -> r
               SyKpred -> r
               SyKclass -> return $ qi $ ClassAsItemType fk
               _ -> return $ qi $ TypeAsItemType fk

matchSymb :: Symbol -> RawSymbol -> Bool
matchSymb sy rsy = let ty = symType sy in
  symName sy == rawSymName rsy && case rsy of
    AnID _ -> True
    AKindedId k _ -> symbTypeToKind ty == k
    ASymbol sy2 -> sy == sy2

instance GetRange RawSymbol where
    getRange = getRange . rawSymName
