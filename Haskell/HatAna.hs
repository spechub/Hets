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
import HsName hiding (HsName)
import Names
import SourceNames
import Relations
import WorkModule
import ScopeModule
import OrigTiMonad -- changed to export TiEnv!
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
import Data.Dynamic

type Sign = TiEnv PNT

type Sentence = HsDeclI PNT

instance ATermConvertible (TiEnv PNT)
instance ATermConvertible (HsDeclI PNT)
instance Typeable (TiEnv PNT)
instance Typeable (HsDeclI PNT)

instance Eq (TiEnv PNT) where
    _ == _ = False

instance Ord (HsDeclI PNT) where
    s1 <= s2 = s1 == s2

instance PrettyPrint (HsDeclI PNT) where
     printText0 _ = text . HatPretty.pp

instance PrintLaTeX (HsDeclI PNT) where
     printLatex0 = printText0

instance Show (TiEnv PNT) where
    show _ = ""

instance PrettyPrint (TiEnv PNT) where
    printText0 _ _ = text ""

instance PrintLaTeX (TiEnv PNT) where
     printLatex0 = printText0

extendTiEnv :: TiEnv PNT -> [TiInstanceDB.Instance PNT]
            -> [TiClasses.TAssump PNT] 
            -> [TiTypes.Assump PNT] -> TiEnv PNT
extendTiEnv e is ts vs = 
      case lift $ extendts vs $
           extendIEnv is $ 
           extendkts ts $ inEnv e $ getEnv of
      Just x -> x
      _ -> error "extendTiEnv"

emptyEnv :: TiEnv PNT
emptyEnv = case lift getEnv of 
                            Just e -> e
                            _ -> error "emptyEnv"

hatAna :: (HsDecls, TiEnv PNT, GlobalAnnos) -> 
          Result (HsDecls, TiEnv PNT, TiEnv PNT, [Named (HsDeclI PNT)])
hatAna (hs@(HsDecls ds), e, _) = 
   case scopeModule (mkWM (emptyRel, emptyRel)
                                :: WorkModuleI QName (SN Id), 
                              [] :: [(ModuleName, Rel (SN Id) (Ent (SN Id)))])
                 $ HsModule loc0 (SN (MainModule "") loc0)
                   Nothing [] ds
   of (sm, _) -> do 
        (HsModule _ _ _ _  fs :>: (is, (ts, vs))) <- lift $ inEnv e $ tcModule 
                      (sm :: HsModuleI (SN ModuleName) PNT [HsDeclI PNT])
        return (hs, extendTiEnv emptyEnv is ts vs, 
                              extendTiEnv e is ts vs, map emptyName fs)

