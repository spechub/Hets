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
import Data.Set

data Sign = Sign 
    { instances :: [TiInstanceDB.Instance PNT]
    , types :: [TiClasses.TAssump PNT]
    , values :: [TiTypes.Assump PNT] 
    , scope :: Rel QName Ents.Entity
    , fixities :: [(HsIdentI (SN Id), HsFixity)] 
    } deriving (Show, Eq)

diffSign :: Sign -> Sign -> Sign
diffSign e1 e2 = 
     emptyEnv { instances = instances e1 \\ instances e2
              , types = types e1 \\ types e2
              , values = values e1 \\ values e2 
              , scope = scope e1 `minusSet` scope e2 
              , fixities = fixities e1 \\ fixities e2
              }

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
        = text "{-" $$ (if null is then empty else
              text "instances:" $$ 
                   vcat (map (text . HatPretty.pp) is)) $$ 
          (if null ts then empty else
              text "\ntypes:" $$ 
                   vcat (map (text . HatPretty.pp) ts)) $$
          (if null vs then empty else
              text "\nvalues:" $$ 
                   vcat (map (text . HatPretty.pp) vs)) $$
          text "-}"

instance PrintLaTeX Sign where
     printLatex0 = printText0

extendSign :: Sign -> [TiInstanceDB.Instance PNT]
            -> [TiClasses.TAssump PNT] 
            -> [TiTypes.Assump PNT] 
            -> Rel QName Ents.Entity
            -> [(HsIdentI (SN Id), HsFixity)]
            -> Sign
extendSign e is ts vs s fs = 
      e { instances = is ++ instances e 
        , types = ts ++ types e
        , values = vs ++ values e 
        , scope = s `union` scope e 
        , fixities = fs ++ fixities e } 

emptyEnv :: Sign
emptyEnv = Sign { instances = []
                , types = []
                , values = [] 
                , scope = emptyRel 
                , fixities = [] }

hatAna :: (HsDecls, Sign, GlobalAnnos) -> 
          Result (HsDecls, Sign, Sign, [Named (HsDeclI PNT)])
hatAna (hs@(HsDecls ds), e, _) = do
   let mn = MainModule ""
       pmod = HsModule loc0 (SN mn loc0) Nothing [] ds
       insc = inscope (toMod pmod) (const emptyRel)
       osc = scope e `union` insc
       wm :: WorkModuleI QName (SN Id)
       wm = mkWM (osc, emptyRel)
       fixs = mapFst getQualified $ getInfixes pmod
       rm = reAssocModule wm [(mn, fixs ++ fixities e)] pmod
       (sm, _) = scopeModule (wm, 
                              [] :: [(ModuleName, Rel (SN Id) (Ent (SN Id)))])
                 rm
   (amod@(HsModule _ _ _ _  fs) :>: (is, (ts, vs))) <- 
            lift $ inMyEnv $ tcModule 
                      (sm :: HsModuleI (SN ModuleName) PNT [HsDeclI PNT])
   return (hs, extendSign emptyEnv is ts vs insc fixs, 
             extendSign e is ts vs insc fixs, map emptyName fs)
   where
   inMyEnv = extendts (values e) 
               . extendkts (types e) 
               . extendIEnv (instances e)     
