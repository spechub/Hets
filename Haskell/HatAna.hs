{-| 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable 

-}

module Haskell.HatAna where

import Common.AS_Annotation 
import Common.Result 
import Common.GlobalAnnotations
import PropPosSyntax hiding (ModuleName, Id)
import TiModule
import HsName
import Names
import SourceNames
import Relations
import WorkModule
import ScopeModule
import OrigTiMonad
import TiTypes
import TiInstanceDB
import TiClasses
import PPfeInstances
import PNT
import Lift
import qualified NewPrettyPrint as HatPretty
import Haskell.HatParser
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.ATerm.Lib
import Common.DynamicUtils
import Data.Dynamic
import Data.List((\\))

data Sign = Sign 
    { instances :: [TiInstanceDB.Instance PNT]
    , types :: [TiClasses.TAssump PNT]
    , values :: [TiTypes.Assump PNT] } deriving (Show, Eq)

diffSign :: Sign -> Sign -> Sign
diffSign e1 e2 = 
     emptyEnv { instances = instances e1 \\ instances e2
              , types = types e1 \\ types e2
              , values = values e1 \\ values e2 }

isSubSign :: Sign -> Sign -> Bool
isSubSign e1 e2 = diffSign e1 e2 == emptyEnv

instance Eq (TypeInfo i) where
    _ == _ = True

type Sentence = HsDeclI PNT

instance ATermConvertible Sign
instance ATermConvertible (HsDeclI PNT)

tyconSign :: TyCon
tyconSign = mkTyCon "Haskell.HatAna.Sign"

instance Typeable Sign where
  typeOf _ = mkTyConApp tyconSign []

tyconPNT :: TyCon
tyconPNT = mkTyCon "Haskell.HatAna.PNT"

instance Typeable PNT where
  typeOf _ = mkTyConApp tyconPNT []

hsDeclItc :: TyCon
hsDeclItc = mkTyCon "Haskell.HatAna.HsDeclI"

instance Typeable i => Typeable (HsDeclI i) where 
  typeOf s = mkTyConApp hsDeclItc [typeOf $ (undefined :: HsDeclI a -> a) s]

instance Ord (HsDeclI PNT) where
    s1 <= s2 = s1 == s2

instance PrettyPrint (HsDeclI PNT) where
     printText0 _ = text . HatPretty.pp

instance PrintLaTeX (HsDeclI PNT) where
     printLatex0 = printText0

instance PrettyPrint Sign where
    printText0 _ Sign { instances = is, types = ts, values = vs }
        = (if null is then empty else
              text "instances:" $$ 
                   vcat (map (text . HatPretty.pp) is)) $$ 
          (if null ts then empty else
              text "types:" $$ 
                   vcat (map (text . HatPretty.pp) ts)) $$
          (if null vs then empty else
              text "values:" $$ 
                   vcat (map (text . HatPretty.pp) vs))

instance PrintLaTeX Sign where
     printLatex0 = printText0

extendTiEnv :: Sign -> [TiInstanceDB.Instance PNT]
            -> [TiClasses.TAssump PNT] 
            -> [TiTypes.Assump PNT] -> Sign
extendTiEnv e is ts vs = 
      e { instances = is ++ instances e 
        , types = ts ++ types e
        , values = vs ++ values e } 

emptyEnv :: Sign
emptyEnv = Sign { instances = []
                , types = []
                , values = [] }

hatAna :: (HsDecls, Sign, GlobalAnnos) -> 
          Result (HsDecls, Sign, Sign, [Named (HsDeclI PNT)])
hatAna (hs@(HsDecls ds), e, _) = 
   case scopeModule (mkWM (emptyRel, emptyRel)
                                :: WorkModuleI QName (SN Id), 
                              [] :: [(ModuleName, Rel (SN Id) (Ent (SN Id)))])
                 $ HsModule loc0 (SN (MainModule "") loc0)
                   Nothing [] ds
   of (sm, _) -> do 
        (HsModule _ _ _ _  fs :>: (is, (ts, vs))) <- 
            lift $ inMyEnv $ tcModule 
                      (sm :: HsModuleI (SN ModuleName) PNT [HsDeclI PNT])
        return (hs, extendTiEnv emptyEnv is ts vs, 
                              extendTiEnv e is ts vs, map emptyName fs)
   where
   inMyEnv = extendts (values e) 
               . extendkts (types e) 
               . extendIEnv (instances e)     
