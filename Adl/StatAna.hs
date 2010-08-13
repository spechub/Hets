{- |
Module      :  $Header$
Description :  static ADL analysis
Copyright   :  (c) Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Adl.StatAna where

import Adl.As
import Adl.Sign

import Common.AS_Annotation
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Result
import Common.Lib.State
import qualified Common.Lib.Rel as Rel

import Control.Monad

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

basicAna :: (Context, Sign, GlobalAnnos)
  -> Result (Context, ExtSign Sign Symbol, [Named Sen])
basicAna (Context m ps, sig, _) =
  let (nps, env) = runState (mapM anaPatElem ps) (toEnv sig)
  in Result (reverse $ msgs env)
     $ Just (Context m nps, ExtSign (sign env) $ syms env, reverse $ sens env)

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
    s = desrc r
    t = detrg r
    in Set.fromList [Con s, Con t, Rel $ Sgn (decnm r) s t]

addRel :: Relation -> State Env ()
addRel r = do
   e <- get
   let s = sign e
       m = rels s
       i = simpleIdToId $ decnm r
       l = Map.findWithDefault Set.empty i m
       v = RelType (desrc r) $ detrg r
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
    else addMsgs [mkDiag Error "unknown GEN" c2]

data TypedRule = TypedRule Rule RelType

anaRule :: Rule -> State Env Rule
anaRule r = do
  s <- gets sign
  case typeRule s r of
    [] -> do
      addMsgs [mkDiag Error "no typing found" r]
      return r
    TypedRule e (RelType c1 c2) : t -> do
      if null t then do
        case c1 of
          Anything -> addMsgs [mkDiag Error "source concept is anything" r]
          _ -> return ()
        case c2 of
          Anything -> addMsgs [mkDiag Error "target concept is anything" r]
          _ -> return ()
        else addMsgs [mkDiag Error "ambiguous typings found" r]
      return e

-- | analyze rule and return resolved one
typeRule :: Sign -> Rule -> [TypedRule]
typeRule s rule =
  let m = rels s
      i = isas s
  in case rule of
   Tm r@(Sgn n rs rt) ->
      if isBRel (tokStr n) then [TypedRule rule $ RelType rs rt] else
      Set.fold
      (\ (RelType f t) l -> maybeToList (do
              a <- compatible i f rs
              b <- compatible i t rt
              return $ TypedRule (Tm r { desrc = a, detrg = b })
                $ RelType a b) ++ l) []
      $ Map.findWithDefault Set.empty (simpleIdToId n) m
   UnExp o r ->
     map (\ (TypedRule e t@(RelType a b)) -> TypedRule (UnExp o e)
          $ if o == Co then RelType b a else t) $ typeRule s r
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
         , let res = case o of
                 Fc -> case compatible i b p of
                         Nothing -> Nothing
                         Just _ -> Just $ RelType a q
                 Fd -> case compatible i a q of
                         Nothing -> Nothing
                         Just _ -> Just $ RelType p b
                 _ -> do
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

anaObject :: Object -> State Env Object
anaObject (Object l r ps os) = do
  e <- anaRule r
  -- the subobject are restricted so this is still wrong
  ns <- mapM anaObject os
  return $ Object l e ps ns

anaPatElem :: PatElem -> State Env PatElem
anaPatElem pe = case pe of
    Pr h u -> do
      nu <- anaRule u
      addSens [case h of
        Always -> makeNamed "" $ Assertion Nothing u
        RuleHeader k t -> makeNamed (show t) $ Assertion (Just k) u]
      return $ Pr h nu
    Pm qs d _ -> do
      addRel d
      addSens $ map (\ q -> makeNamed (show (decnm d) ++ "_"
                                       ++ showUp (propProp q))
                    $ DeclProp d q) qs
      return pe
    Pg c1 c2 -> do
      addIsa c1 c2
      return pe
    Pk (KeyDef l c atts) -> do
       ssyms <- gets $ symOf . sign
       unless (Set.member (Con c) ssyms) $
         addMsgs [mkDiag Error "unknown KEY concept" c]
       natts <- mapM anaAtts atts
       return $ Pk $ KeyDef l c natts
    Plug p o -> do
      n <- anaObject o
      return $ Plug p n
    _ -> return pe
