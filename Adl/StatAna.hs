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

import qualified Data.Set as Set
import qualified Data.Map as Map

basicAna :: (Context, Sign, GlobalAnnos)
  -> Result (Context, ExtSign Sign Symbol, [Named Sen])
basicAna (c@(Context _ ps), sig, _) =
  let env = execState (mapM_ anaPatElem ps) (toEnv sig)
  in Result (msgs env) $ Just (c, ExtSign (sign env) $ syms env, sens env)

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

anaPatElem :: PatElem -> State Env ()
anaPatElem pe = case pe of
    Pr h u -> addSens [case h of
      Always -> makeNamed "" $ Assertion Nothing u
      RuleHeader k t -> makeNamed (show t) $ Assertion (Just k) u]
    Pm qs d _ -> do
      addRel d
      addSens $ map (\ q -> makeNamed (show (decnm d) ++ "_"
                                       ++ showUp (propProp q))
                    $ DeclProp d q) qs
    Pg c1 c2 -> addIsa c1 c2
    _ -> return ()
