{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable 

-}

module Haskell.HatAna (module Haskell.HatAna, PNT, HsDeclI) where

import Common.AS_Annotation 
import Common.Result 
import Common.GlobalAnnotations
import PropPosSyntax hiding (Id, HsName)
import Modules
import MUtils
import ReAssocModule
import AST4ModSys
import HsName
import ReAssocBase
import Names
import Ents
import SourceNames
import Relations
import WorkModule
import ScopeModule
import OrigTiMonad
import TypedIds(namespace)
import HasBaseName
import TiNames
import TiTypes
import TiInstanceDB
import TiClasses
import HsConstants
import PPfeInstances()
import PNT
import Lift
import qualified NewPrettyPrint as HatPretty
import Haskell.HatParser
import Common.PrettyPrint
import Common.Lib.Pretty
import Data.List((\\))
import Data.Set
import qualified Common.Lib.Map as Map

type Scope = Rel (SN HsName) (Ent (SN Id))

data Sign = Sign 
    { instances :: [Instance PNT]
    , types :: Map.Map (HsIdentI PNT) (Kind, TypeInfo PNT)
    , values :: Map.Map (HsIdentI PNT) (Scheme PNT) 
    , scope :: Scope
    , fixities :: Map.Map (HsIdentI (SN Id)) HsFixity
    } deriving (Show, Eq)

diffSign :: Sign -> Sign -> Sign
diffSign e1 e2 = emptySign 
    { instances = instances e1 \\ instances e2
    , types = types e1 `Map.difference` types e2
    , values = values e1 `Map.difference` values e2 
    , scope = scope e1 `minusRel` scope e2 
    , fixities = fixities e1 `Map.difference` fixities e2
    }

addSign :: Sign -> Sign -> Sign
addSign e1 e2 = emptySign 
    { instances = let is = instances e2 in (instances e1 \\ is) ++ is
    , types = types e1 `Map.union` types e2
    , values = values e1 `Map.union` values e2 
    , scope = scope e1 `union` scope e2 
    , fixities = fixities e1 `Map.union` fixities e2
    }

isSubSign :: Sign -> Sign -> Bool
isSubSign e1 e2 = diffSign e1 e2 == emptySign

instance Eq (TypeInfo i) where
    _ == _ = True

instance Ord (HsDeclI PNT) where
    s1 <= s2 = s1 == s2

instance PrettyPrint (HsDeclI PNT) where
     printText0 _ = text . HatPretty.pp

instance PrettyPrint Sign where
    printText0 _ Sign { instances = is, types = ts, 
                        values = vs, fixities = fs, scope = sc }
        = text "{-" $$ (if null is then empty else
              text "instances:" $$ 
                   vcat (map (text . HatPretty.pp) is)) $$ 
          (if Map.isEmpty ts then empty else
              text "\ntypes:" $$ 
                   vcat (map (text . HatPretty.pp) 
                         [ a :>: b | (a, b) <- Map.toList ts ])) $$
          (if Map.isEmpty vs then empty else
              text "\nvalues:" $$ 
                   vcat (map (text . HatPretty.pp) 
                         [ a :>: b | (a, b) <- Map.toList vs ])) $$
          (if Map.isEmpty fs then empty else
              text "\nfixities:" $$ 
                   vcat [ text (HatPretty.pp b) <+> text (HatPretty.pp a) 
                              | (a, b) <- Map.toList fs ]) $$
          text "\nscope:" $$ 
          text (HatPretty.pp sc) $$
          text "-}" $$
          text "module Dummy where"
          $$ text "import Prelude (error, Show, Eq, Ord)"
          $$ text "import MyLogic"



extendSign :: Sign -> [TiInstanceDB.Instance PNT]
            -> [TiClasses.TAssump PNT] 
            -> [TiTypes.Assump PNT] 
            -> Scope
            -> [(HsIdentI (SN Id), HsFixity)]
            -> Sign
extendSign e is ts vs s fs = addSign e emptySign 
    { instances = is 
    , types = Map.fromList [ (a, b) | (a :>: b) <- ts ]
    , values = Map.fromList [ (a, b) | (a :>: b) <- vs ] 
    , scope = s
    , fixities = Map.fromList fs 
    } 

emptySign :: Sign
emptySign = Sign 
    { instances = []
    , types = Map.empty
    , values = Map.empty 
    , scope = emptyRel 
    , fixities = Map.empty 
    }

hatAna :: (HsDecls, Sign, GlobalAnnos) -> 
          Result (HsDecls, Sign, Sign, [Named (HsDeclI PNT)])
hatAna (hs@(HsDecls ds), e, _) = do
   let parsedMod = HsModule loc0 (SN mod_Prelude loc0) Nothing [] ds
       astMod = toMod parsedMod
       insc = inscope astMod (const emptyRel)
       osc = scope e `union` insc
       expScope :: Rel (SN Id) (Ent (SN Id))
       expScope = mapDom (fmap hsUnQual) osc
       wm :: WorkModuleI QName (SN Id)
       wm = mkWM (osc, expScope)
       fixs = mapFst getQualified $ getInfixes parsedMod
       fixMap = Map.fromList fixs `Map.union` fixities e
       rm = reAssocModule wm [(mod_Prelude, Map.toList fixMap)] parsedMod
       (HsModule _ _ _ _ sds, _) = 
           scopeModule (wm, [(mod_Prelude, expScope)]) rm
       ent2pnt (Ent m (HsCon i) t) = 
           HsCon (topName Nothing m (bn i) (origt m t))
       ent2pnt (Ent m (HsVar i) t) = 
           HsVar (topName Nothing m (bn i) (origt m t))
       bn i = getBaseName i
       origt m = fmap (osub m) 
       osub m n = origName n m n
       findPredef ns (_, n) = 
           case filter ((==ns) . namespace) $ applyRel expScope (fakeSN n) of
           [v] -> Right (ent2pnt v)
           _ -> Left ("'" ++ n ++ "' unknown or ambiguous")
       inMyEnv =  withStdNames findPredef
               . inModule (const mod_Prelude) []
               . extendts [ a :>: b | (a, b) <- Map.toList $ values e ] 
               . extendkts [ a :>: b | (a, b) <- Map.toList $ types e ] 
               . extendIEnv (instances e)
   fs :>: (is, (ts, vs)) <- 
        lift $ inMyEnv $ tcTopDecls id sds
   let accSign = extendSign e is ts vs insc fixs
   return (hs, diffSign accSign e, accSign, map emptyName fs)

