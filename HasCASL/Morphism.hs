{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (deriving Typeable)
    
Morphism on 'Env' (as for CASL)
-}

module HasCASL.Morphism where

import HasCASL.Le
import HasCASL.As
import HasCASL.Merge
import HasCASL.Symbol
import Common.Id
import Common.Result
import Data.Dynamic
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map

data SymbolType = OpAsItemType TypeScheme 
		| TypeAsItemType Kind
		| ClassAsItemType
		  deriving (Show, Eq, Ord)

instance Ord TypeScheme where
    t1 <= t2 = t1 == t2 || show t1 < show t2

data Symbol = Symbol {symName :: Id, symbType :: SymbolType} 
	      deriving (Show, Eq, Ord, Typeable)

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId SymbKind Id
    	         deriving (Show, Eq, Ord, Typeable)

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

symbTypeToKind :: SymbolType -> SymbKind
symbTypeToKind (OpAsItemType _) = SK_op
symbTypeToKind (TypeAsItemType _)     = SK_type
symbTypeToKind ClassAsItemType      = SK_class

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw (Symbol idt typ) = AKindedId (symbTypeToKind typ) idt

statSymbMapItems :: [SymbMapItems] -> Result (Map.Map RawSymbol RawSymbol)
statSymbMapItems sl =  return (Map.fromList $ concat $ map s1 sl)
  where
  s1 (SymbMapItems kind l _ _) = map (symbOrMapToRaw kind) l
 
symbOrMapToRaw :: SymbKind -> SymbOrMap -> (RawSymbol,RawSymbol)
symbOrMapToRaw k (SymbOrMap s mt _) = 
    (symbToRaw k s,
     symbToRaw k $ case mt of Nothing -> s
                              Just t -> t)

statSymbItems :: [SymbItems] -> Result [RawSymbol]
statSymbItems sl = 
  return (concat (map s1 sl))
  where s1 (SymbItems kind l _ _) = map (symbToRaw kind) l

symbToRaw :: SymbKind -> Symb -> RawSymbol
symbToRaw k (Symb idt _ _)     = symbKindToRaw k idt

symbKindToRaw :: SymbKind -> Id -> RawSymbol
symbKindToRaw Implicit     idt = AnID idt
symbKindToRaw sk idt = AKindedId sk idt

matchSymb :: Symbol -> RawSymbol -> Bool
matchSymb x                            (ASymbol y)              =  x==y
matchSymb (Symbol idt _)                (AnID di)               = idt==di
matchSymb (Symbol idt _)        (AKindedId _ di)                = idt==di

data Morphism = Morphism {msource,mtarget :: Env}
                         deriving (Eq, Show, Typeable)

mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism e1 e2

ideMor :: Env -> Morphism
ideMor e = mkMorphism e e  -- plus identity functions
compMor :: Morphism -> Morphism -> Morphism
compMor m1 m2 = Morphism (msource m1) (mtarget m2) -- plus composed functions

inclusionMor :: Env -> Env -> Result Morphism
inclusionMor e1 e2 = return (mkMorphism e1 e2)

legalEnv :: Env -> Bool
legalEnv _ = True -- maybe a closure test?
legalMor :: Morphism -> Bool
legalMor m = legalEnv (msource m) && legalEnv (mtarget m)  -- and what else?

morphismUnion :: Morphism -> Morphism -> Result Morphism
morphismUnion m1 m2 = do s <- merge (msource m1) $ msource m2
			 t <- merge (mtarget m1) $ mtarget m2
			 return $ mkMorphism s t


-- Some quick and dirty instances

instance PrettyPrint Morphism where
  printText0 ga s = text (show s)

instance PrettyPrint Symbol where
  printText0 ga s = text (show s)

instance PrettyPrint RawSymbol where
  printText0 ga s = text (show s)
