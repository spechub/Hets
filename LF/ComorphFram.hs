module LF.ComorphFram
   ( mapTheory
   , mapMorphism
   , mapSen
   , mapSymb
   ) where

import LF.Morphism
import LF.Sign

import Common.Result
import Common.DocUtils
import Common.AS_Annotation

import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe, isNothing)

mapTheory :: Morphism -> (Sign, [Named EXP]) -> Result (Sign, [Named EXP])
mapTheory mor (s1, ne) =
  let s2 = mapSign mor s1
      ne2 = map (mapNamedSent mor) ne
  in return (s2, ne2)

mapNamedSent :: Morphism -> Named EXP -> Named EXP
mapNamedSent mor ne = ne {sentence = mapSent mor $ sentence ne}

mapMorphism :: Morphism -> Morphism -> Result Morphism
mapMorphism mor m1 =
  let s1 = source m1
      t1 = target m1
      t2 = mapSign mor t1
      defs1 = filter (\ (Def _ _ v) -> isNothing v) $ getDefs s1
      (defs2, m2) = makeSigMap ([], Map.empty) $ map (mapMorphH mor)
                      (mkPairs defs1 $ symMap m1)
      s2 = Sign gen_base gen_module defs2
  in return $ Morphism gen_base gen_module gen_morph s2 t2 Unknown m2

mapMorphH :: Morphism -> (DEF, EXP) -> (DEF, Maybe EXP)
mapMorphH mor (Def sym stp _ , e) =
  case mapSymbH mor sym stp of
       Right sym2 -> let stp2 = mapSent mor stp
                         e2 = mapSent mor e
                         sval2 = takeSymValue sym2 $ getDefs $ target mor
                     in case sval2 of
                             Nothing -> (Def sym2 stp2 Nothing, Just e2)
                             _ -> (Def sym2 stp2 sval2, Nothing)
       Left err -> error $ show err

mkPairs :: [DEF] -> Map.HashMap Symbol EXP -> [(DEF, EXP)]
mkPairs defs m = case defs of
   [] -> []
   Def s t v : ds -> case Map.lookup s m of
                                  Just e -> (Def s t v, e) : mkPairs ds m
                                  Nothing -> error $ "mkPairs : " ++
-- "The symbol "
                                                        show (pretty s) ++
                                                        " is not in the map.\n"

makeSigMap :: ([DEF], Map.HashMap Symbol EXP) -> [(DEF, Maybe EXP)]
               -> ([DEF], Map.HashMap Symbol EXP)
makeSigMap dms defs = case defs of
   [] -> dms
   (Def s t v, e) : des -> let (ds, m) = dms
                             in case e of
                                     Just e' -> makeSigMap (Def s t v : ds,
                                                 Map.insert s e' m) des
                                     Nothing -> makeSigMap (Def s t v : ds, m) des


mapSign :: Morphism -> Sign -> Sign
mapSign mor sig =
  let ds = filter (\ (Def _ _ v) -> isNothing v) $ getDefs sig
      defs = mapDefs mor ds
  in Sign gen_base gen_module defs

mapDefs :: Morphism -> [DEF] -> [DEF]
mapDefs mor defs = case defs of
  [] -> []
  Def s t _ : ds -> case mapSymbH mor s t of
                  Right s2 -> let t2 = mapSent mor t
                                  sval = takeSymValue s2 $ getDefs $ target mor
                              in Def s2 t2 sval : mapDefs mor ds
                  Left err -> error $ show err

takeSymValue :: Symbol -> [DEF] -> Maybe EXP
takeSymValue sym defs = case defs of
   [] -> Nothing
   Def sym2 _ val : ds -> if sym == sym2
                              then val
                              else takeSymValue sym ds


mapSymb :: Morphism -> Sign -> Symbol -> Set.Set Symbol
mapSymb mor sig sym = Set.singleton $ mapSymb' mor sig sym

mapSymb' :: Morphism -> Sign -> Symbol -> Symbol
mapSymb' mor sig sym =
   let symType = getSymType sym sig
   in case symType of
           Just symT -> case mapSymbH mor sym symT of
                             Right s -> s
                             Left err -> error $ "mapSymb' : " ++ show err
           Nothing -> error $ "mapSymb' : The symbol " ++
                              show (pretty sym) ++
                              " is not in the signature.\n"

mapSymbH :: Morphism -> Symbol -> EXP -> Either String Symbol
mapSymbH mor sym symType' =
   let sig2 = target mor
       symType = mapSent mor symType'
   in if Just symType == getSymType sym sig2
         then Right sym
         else let syms = getSymsOfType symType sig2
              in case Set.toList syms of
                      [s'] -> Right s'
                      [] -> Left $ noSymError sym symType
                      _ -> let locals = getLocalSyms sig2
                               inter = Set.intersection syms locals
                           in case Set.toList inter of
                                   [s'] -> Right s'
                                   [] -> Left $ noSymError sym symType
                                   _ -> Left $ manySymError sym symType


mapSen :: Morphism -> EXP -> Result EXP
mapSen mor ex = return $ mapSent mor ex

mapSent :: Morphism -> EXP -> EXP
mapSent m e =
  let re = translate m e
  in fromMaybe (error $ "The sentence morphism" ++
                        "could not be performed.\n") re

{-
-- mapSent synM lmod_target lmod_source modM e
mapSent :: Morphism -> Morphism -> Morphism -> Morphism -> EXP -> Result EXP
mapSent synM lmodTarget lmodSource modM e =
  let route1 = compMorph synM lmodTarget
      route2 = compMorph lmodSource modM
      em1 = translate route1 e
      em2 = translate route2 e
      if (em1 == em2)
         then let re = translate synM e
              in  case re of
                       Nothing -> fail $ "The sentence morphism" ++
                                         "could not be performed.\n"
                       Just ex -> ex
         else fail $
-}


-- ERROR MESSAGES
noSymError :: Symbol -> EXP -> String
noSymError s t = "Symbol " ++ show (pretty s) ++
   " cannot be mapped to anything as the target signature contains" ++
   " no symbols of type/kind " ++ show (pretty t) ++ "."

manySymError :: Symbol -> EXP -> String
manySymError s t = "Symbol " ++ show (pretty s) ++
   " cannot be mapped to anything as the target signature contains" ++
   " more than one symbol of type/kind " ++ show (pretty t) ++ "."
