{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
  raw symbols bridge symb items and the symbols of a signature
-}

module HasCASL.RawSym where

import HasCASL.As
import HasCASL.Le
import HasCASL.Symbol
import HasCASL.SymbItem
import HasCASL.TypeAna
import HasCASL.OpDecl
import HasCASL.Unify
import HasCASL.Builtin
import Common.Id
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Lib.State
import qualified Common.Lib.Map as Map

data RawSymbol = AnID Id | AKindedId SymbKind Id 
	       | AQualId Id SymbolType
    	         deriving (Show, Eq, Ord)

-- note that the type of a raw symbol is not analysed!

instance PrettyPrint RawSymbol where
  printText0 ga rs = case rs of
      AnID i -> printText0 ga i
      AKindedId k i -> printSK k <> printText0 ga i
      AQualId i t -> printSK (symbTypeToKind t) <> printText0 ga i <+> colon 
		       <+> printText0 ga t

type RawSymbolMap = Map.Map RawSymbol RawSymbol

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

rawSymName :: RawSymbol -> Id
rawSymName (AnID i) = i
rawSymName (AKindedId _ i) = i
rawSymName (AQualId i _) = i

symbTypeToKind :: SymbolType -> SymbKind
symbTypeToKind (OpAsItemType _)    = SK_op
symbTypeToKind (TypeAsItemType _)  = SK_type
symbTypeToKind (ClassAsItemType _) = SK_class

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw sym = AQualId (symName sym) $ symType sym

statSymbMapItems :: [SymbMapItems] -> Result RawSymbolMap
statSymbMapItems sl = do 
    rs <- mapM ( \ (SymbMapItems kind l _ _)
		 -> mapM (symbOrMapToRaw kind) l) sl
    foldr ( \ (r1, r2) mm -> do
	    m <- mm
	    if Map.member r1 m then do 
	        Result [Diag Error ("duplicate mapping for: " ++ 
			  showPretty r1 "\n ignoring: " ++ showPretty r2 "")
		       $ posOfId $ rawSymName r2] $ Just ()
	        return m
	      else return $ Map.insert r1 r2 m) 
	  (return Map.empty) $ concat rs
 
symbOrMapToRaw :: SymbKind -> SymbOrMap -> Result (RawSymbol, RawSymbol)
symbOrMapToRaw k (SymbOrMap s mt _) = do
    s1 <- symbToRaw k s  
    s2 <- symbToRaw k $ case mt of Nothing -> s
				   Just t -> t
    return (s1, s2)

statSymbItems :: [SymbItems] -> Result [RawSymbol]
statSymbItems sl = do rs <- mapM (\ (SymbItems kind l _ _) 
				  -> mapM (symbToRaw kind) l) sl
		      return $ concat rs

symbToRaw :: SymbKind -> Symb -> Result RawSymbol
symbToRaw k (Symb idt mt _)     = case mt of 
    Nothing -> return $ symbKindToRaw k idt
    Just (SymbType sc@(TypeScheme vs (_ :=> t) _)) -> 
	let r = return $ AQualId idt $ OpAsItemType sc
	    rk = if null vs then Nothing else 
		 convertTypeToKind t 
	    rrk = maybeToResult (getMyPos t) 
	                   ("not a kind: " ++ showPretty t "") rk
	in case k of 
	      SK_op -> r
	      SK_fun -> r
	      SK_pred -> return $ AQualId idt $ OpAsItemType
			 $ predTypeScheme sc
	      SK_class -> do ck <- rrk
			     return $ AQualId idt $ ClassAsItemType ck
	      _ -> do ck <- rrk
		      return $ AQualId idt $ TypeAsItemType ck

convertTypeToKind :: Type -> Maybe Kind
convertTypeToKind (FunType t1 FunArr t2 ps) = 
    do k1 <- convertTypeToKind t1
       k2 <- convertTypeToKind t2
       case k2 of 
	       ExtKind _ _ _ -> Nothing
	       _ -> Just $ FunKind k1 k2 ps

convertTypeToKind (BracketType Parens [] _) = 
    Nothing
convertTypeToKind (BracketType Parens [t] _) = 
    convertTypeToKind t
convertTypeToKind (BracketType Parens ts ps) = 
       do ks <- mapM convertTypeToKind ts
	  Just $ Intersection ks ps

convertTypeToKind (MixfixType [t1, TypeToken t]) = 
    let s = tokStr t 
	v = case s of 
		   "+" -> CoVar 
		   "-" -> ContraVar 
		   _ -> InVar
    in case v of 
	      InVar -> Nothing
	      _ -> do k1 <- convertTypeToKind t1
		      Just $ ExtKind k1 v [tokPos t]
convertTypeToKind(TypeToken t) = 
       if tokStr t == "Type" then Just $ Universe [tokPos t] else
          let ci = simpleIdToId t in
          Just $ ClassKind ci MissingKind
convertTypeToKind _ = Nothing

symbKindToRaw :: SymbKind -> Id -> RawSymbol
symbKindToRaw Implicit = AnID 
symbKindToRaw sk = AKindedId $ case sk of 
		   SK_pred -> SK_op
		   SK_fun -> SK_op
		   SK_sort -> SK_type
		   _ -> sk

matchSymb :: Symbol -> RawSymbol -> Bool
matchSymb sy rsy = let ty = symType sy in 
    symName sy == rawSymName rsy && 
       (case rsy of 
		AnID _ -> True
		AKindedId k _ -> symbTypeToKind ty == k
		AQualId _ t -> matchSymbType (symEnv sy) ty t)

anaSymbolType :: SymbolType -> State Env (Maybe SymbolType)
anaSymbolType t = 
    case t of 
    ClassAsItemType k -> do ak <- fromResult $ anaKindM k
			    return $ fmap ClassAsItemType ak
    TypeAsItemType k -> do ak <- fromResult $ anaKindM k
			   return $ fmap TypeAsItemType ak
    OpAsItemType sc -> do as <- anaTypeScheme sc
			  return $ fmap OpAsItemType as	

matchSymbType :: Env -> SymbolType -> SymbolType -> Bool
matchSymbType e t1 t2 = 
    let mt = evalState (anaSymbolType t2) e {typeMap = addUnit $ typeMap e}
	in case mt of 
    Nothing -> False
    Just t -> compSymbType (typeMap e) t1 t

compSymbType :: TypeMap -> SymbolType -> SymbolType -> Bool
compSymbType tm t1 t2 = 
    case (t1, t2) of 
    (ClassAsItemType k1, ClassAsItemType k2) -> k1 == k2
    (TypeAsItemType k1, TypeAsItemType k2) -> k1 == k2
    (OpAsItemType s1, OpAsItemType s2) -> isUnifiable tm 0 s1 s2
    _ -> False
