{- |
Module      :  $Header$
Description :  static ADL analysis
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.StatAna where

import Adl.As
import Adl.Sign

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.Lib.State
import qualified Common.Lib.Rel as Rel
import Common.Utils

import Control.Monad

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.List

basicAna :: (Context, Sign, GlobalAnnos)
  -> Result (Context, ExtSign Sign Symbol, [Named Sen])
basicAna (Context m ps, sig, _) =
  let (nps, env) = runState (mapM anaPatElem ps) $ toEnv sig
  in Result (reverse $ msgs env)
     $ Just (Context m nps, ExtSign (closeSign $ sign env) $ syms env
            , reverse $ sens env)

data Env = Env
  { sign :: Sign
  , syms :: Set.Set Symbol
  , sens :: [Named Sen]
  , msgs :: [Diagnosis]
  }

toEnv :: Sign -> Env
toEnv s = Env { sign = s, syms = Set.empty, sens = [], msgs = [] }

addMsgs :: [Diagnosis] -> State Env ()
addMsgs ds = do
   e <- get
   put e { msgs = ds ++ msgs e }

addSens :: [Named Sen] -> State Env ()
addSens ns = do
   e <- get
   put e { sens = ns ++ sens e }

addSyms :: Set.Set Symbol -> State Env ()
addSyms sys = do
   e <- get
   put e { syms = Set.union sys $ syms e }

symsOf :: Relation -> Set.Set Symbol
symsOf r = let
    y = relType r
    s = relSrc y
    t = relTrg y
    in Set.fromList [Con s, Con t, Rel r]

addRel :: Relation -> State Env ()
addRel r = do
   e <- get
   let s = sign e
       m = rels s
       i = simpleIdToId $ decnm r
       l = Map.findWithDefault Set.empty i m
       v = relType r
   put e { sign = s { rels = Map.insert i (Set.insert v l) m } }

addIsa :: Concept -> Concept -> State Env ()
addIsa c1 c2 = do
   e <- get
   let s = sign e
       r = isas s
       sys = symOf s
   if Set.member (Con c1) sys then
      if Set.member (Con c2) sys then
         if c1 == c2 then addMsgs [mkDiag Warning "no specialization" c1]
         else if Rel.path c2 c1 r then
                  addMsgs [mkDiag Error "opposite ISA known" c1]
              else if Rel.path c1 c2 r then
                       addMsgs [mkDiag Hint "redeclared ISA" c1]
                   else put e { sign = s { isas = Rel.insert c1 c2 r }}
      else addMsgs [mkDiag Error "unknown ISA" c2]
    else addMsgs [mkDiag Error "unknown GEN" c1]

data TypedRule = TypedRule Rule RelType deriving Show

instance Pretty TypedRule where
  pretty (TypedRule r (RelType c1 c2)) =
    fsep [pretty r <+> text "::", pretty c1 <+> cross <+> pretty c2]

anaRule :: Rule -> State Env Rule
anaRule r = do
  s <- gets sign
  case typeRule s r of
    [] -> do
      addMsgs [mkDiag Error "no typing found" $ findTypeFailure s r]
      return r
    l@(TypedRule e (RelType c1 c2) : t) -> do
      if null t then do
        case c1 of
          Anything -> addMsgs [mkDiag Error "source concept is anything" r]
          _ -> return ()
        case c2 of
          Anything -> addMsgs [mkDiag Error "target concept is anything" r]
          _ -> return ()
        else addMsgs [Diag Error
          (unlines $ "ambiguous typings found:"
            : map (`showDoc` "") l) $ getRangeSpan r]
      return e

findTypeFailure :: Sign -> Rule -> Rule
findTypeFailure s r = case r of
  Tm _ -> r
  UnExp _ e -> if null (typeRule s e) then findTypeFailure s e else r
  MulExp o es -> case es of
    [] -> error "findTypeFailure"
    e : t ->
      if null (typeRule s e) then findTypeFailure s e else
      if null t then e else let n = MulExp o t in
      if null (typeRule s n) then findTypeFailure s n else r

-- | analyze rule and return resolved one
typeRule :: Sign -> Rule -> [TypedRule]
typeRule s rule =
  let m = rels s
      i = isas s
  in case rule of
   Tm (Sgn n ty@(RelType rs rt)) -> let str = tokStr n in
      if str == "V" then [TypedRule rule ty] else
      if str == "I" then case (rs, rt) of
        (Anything, Anything) ->
          map (\ c -> let y = RelType c c in TypedRule (Tm $ Sgn n y) y)
          . keepMins (flip $ isSubConcept i) . Set.toList $ conceptsOf s
        _ -> case compatible i rs rt of
          Just c -> let y = RelType c c in [TypedRule (Tm $ Sgn n y) y]
          Nothing -> []
      else Set.fold
      (\ (RelType f t) l -> maybeToList (do
              a <- compatible i f rs
              b <- compatible i t rt
              let y = RelType a b
              return $ TypedRule (Tm $ Sgn n y) y) ++ l) []
      $ Map.findWithDefault Set.empty (simpleIdToId n) m
   UnExp o r -> concatMap
     (\ (TypedRule e t@(RelType a b)) -> map (TypedRule $ UnExp o e)
          $ case o of
              Co -> [RelType b a]
              Cp -> [t]
              _ -> case compatible i a b of
                     Nothing -> []
                     Just c -> [RelType c c]
     ) $ typeRule s r
   MulExp o es -> case es of
     [] -> error "typeRule"
     r : t -> if null t then typeRule s r else
       let rs = typeRule s r
           ts = typeRule s $ MulExp o t
       in
         [ TypedRule fe ty
         | TypedRule ne (RelType a b) <- rs
         , TypedRule re (RelType p q) <- ts
         , let fe = case re of
                 MulExp op nt | op == o -> MulExp o $ ne : nt
                 _ -> MulExp o [ne, re]
         , let res = if elem o [Fc, Fd] then
                 case compatible i b p of
                         Nothing -> Nothing
                         Just _ -> Just $ RelType a q
                 else do
                   na <- compatible i a p
                   nb <- compatible i b q
                   return $ RelType na nb
         , Just ty <- [res]]

compatible :: Rel.Rel Concept -> Concept -> Concept -> Maybe Concept
compatible r c1 c2 = case () of
  _ | isSubConcept r c1 c2 -> Just c1
    | isSubConcept r c2 c1 -> Just c2
  _ -> Nothing

isSubConcept :: Rel.Rel Concept -> Concept -> Concept -> Bool
isSubConcept r c1 c2 = c1 == c2 || case c2 of
  Anything -> True
  _ -> Rel.path c1 c2 r

anaAtts :: KeyAtt -> State Env KeyAtt
anaAtts (KeyAtt m r) = do
  n <- anaRule r
  return $ KeyAtt m n

conceptsOf :: Sign -> Set.Set Concept
conceptsOf = Set.fold (\ sy -> case sy of
  Con c -> Set.insert c
  _ -> id) Set.empty . symOf

anaObject :: Object -> State Env ()
anaObject (Object _ r _ os) = do
  anaRule r
  mapM_ (anaObject . \ o -> o { expr = MulExp Fc [r, expr o]}) os

anaPatElem :: PatElem -> State Env PatElem
anaPatElem pe = case pe of
    Pr h u -> do
      nu <- anaRule u
      addSens [case h of
        Always -> makeNamed "" $ Assertion Nothing nu
        RuleHeader k t -> makeNamed (show t) $ Assertion (Just k) nu]
      return $ Pr h nu
    Pm qs d@(Sgn _ ty@(RelType c1 c2)) b -> do
      addRel d
      let (nqs, ws) = if c1 == c2 then (qs, []) else
            partition ((< Sym) . propProp) qs
      addMsgs $ map (mkDiag Error $ "bad concepts "
                     ++ showDoc ty " with property") ws
      addSens $ map (\ q -> makeNamed (show (decnm d) ++ "_"
                                       ++ showUp (propProp q))
                    $ DeclProp d q) nqs
      return $ Pm nqs d b
    Pg c1 c2 -> do
      addIsa c1 c2
      return pe
    Pk (KeyDef l c atts) -> do
       csyms <- gets $ conceptsOf . sign
       unless (Set.member c csyms) $
         addMsgs [mkDiag Error "unknown KEY concept" c]
       natts <- mapM anaAtts atts
       return $ Pk $ KeyDef l c natts
    Plug _ o -> do
      anaObject o
      return pe
    _ -> return pe
