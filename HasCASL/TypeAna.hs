
{- HetCATS/HasCASL/TypeAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse given classes and types
-}

module TypeAna where

import As
import AsUtils
import ClassAna
import Id
import Le
import List
import Maybe
import MonadState
import PrintAs()
import FiniteMap
import Result

checkTypeKind :: Id -> Kind -> State Env [Diagnosis]
checkTypeKind i k = 
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> return [Diag Error 
		      ("unknown type '" ++ showId i "'")
				   (posOfId i)]
	   Just ks -> return $ eqKindDiag k $ head ks

anaTypeId :: Id -> State Env Type 
anaTypeId i = 
    do tk <- getTypeKinds
       appendDiags $ case lookupFM tk i of
         Nothing -> [Diag Error ("undeclared type '" ++ showId i "'")
		    $ posOfId i]
	 _ -> []
       return $ TypeConstrAppl i 0 Nothing [] []

mkTypeConstrAppls :: Type -> State Env Type
mkTypeConstrAppls (TypeConstrAppl i v k ts ps) = 
    do newTs <- mapM mkTypeConstrAppls ts
       return $ TypeConstrAppl i v k newTs ps
mkTypeConstrAppls (TypeToken t) = return $
    TypeConstrAppl (simpleIdToId t) 0 Nothing [] []
mkTypeConstrAppls t@(BracketType b ts ps) =
    do args <- mapM mkTypeConstrAppls ts
       let toks@[o,c] = mkBracketToken b ps 
	   i = if null ts then Id toks [] [] 
	       else Id [o, Token place $ posOfType $ head ts, c] [] []
	   res = TypeConstrAppl i 0 Nothing args []
       if null ts then return res
	  else if null $ tail ts then
	       return $ case b of 
			       Parens -> head args
			       _ -> res
	       else do appendDiags [Diag Error
				       ("illegal type: " ++ 
					showPretty t "")
				      $ posOfType t]
		       return res

mkTypeConstrAppls (MixfixType (f:a)) =
   do newF <- mkTypeConstrAppls f 
      newA <- mapM mkTypeConstrAppls a
      return $ MixfixType $ newF : newA
 

mkTypeConstrAppls (KindedType t k p) =
    do newT <- mkTypeConstrAppls t
       return $ KindedType newT k p

mkTypeConstrAppls (LazyType t p) =
    do newT <- mkTypeConstrAppls t
       return $ LazyType newT p

mkTypeConstrAppls (ProductType ts ps) =
    do newTs <- mapM mkTypeConstrAppls ts
       return $ ProductType newTs ps

mkTypeConstrAppls (FunType t1 a t2 ps) =
    do newT1 <- mkTypeConstrAppls t1
       newT2 <- mkTypeConstrAppls t2
       return $ FunType newT1 a newT2 ps

getIdKind :: TypeKinds -> Id -> Maybe Kind
getIdKind tk i = 
       case lookupFM tk i of
       Nothing -> Nothing
       Just ks -> Just $ head ks 

getKind :: TypeKinds -> Id -> Maybe Kind
getKind tk i = 
       case lookupFM tk i of
       Nothing -> Nothing
       Just ks -> Just $ head ks 
    

anaType :: Type -> State Env Type
anaType (t@(TypeConstrAppl i v k ts _)) = do
    let e1 = case k of
	     Nothing -> []
	     Just kind -> if length ts > kindArity kind then
			  [Diag Error ("too many type arguments:\n" ++
				       indent 2 (showPretty t) "")
			   (posOfType t)] else []
	e2 = if v > 0 then 
	     [Diag Error 
	      ("uninstantiated generic variable " ++
	       showId i "")
	      (posOfId i)] else []
--    ds <- checkTypeKind i k
    appendDiags $ e1 ++ e2
    return t

anaType (TypeToken t) = 
    
    anaTypeId $ simpleIdToId t

anaType (BracketType Parens ts ps) =
    do newTs <- mapM anaType ts
       return $ ProductType newTs ps

anaType (BracketType b ts ps) = do
    let toks@[o,c] = mkBracketToken b ps 
	i = if null ts then Id toks [] [] 
	    else Id [o, Token place $ posOfType $ head ts, c] [] []
    newT <- anaTypeId i
    if null ts then return newT
	  else do args <- mapM anaType ts
		  case newT of
			   TypeConstrAppl _ _ (Just k) _ _ -> 
			       do if kindArity k < length args then
				     appendDiags [Diag Error 
						  ("too many arguments for '"
						   ++ showId i "'")
						 $ posOfId i]
				     else return ()
				  return $ TypeConstrAppl i 0 (Just k) args []
			   _ -> return $ TypeConstrAppl i 0 Nothing args []

anaType(KindedType t k ps) =
    do newK <- anaKind k
       newT <- anaType t
       -- getKind of t and compare it with k
       return $ KindedType newT newK ps

anaType (MixfixType ts) = 
    do (f:as) <- mapM anaType ts
       return $ case f of 
	      TypeConstrAppl i g k bs _ ->
		  TypeConstrAppl i g k (bs ++ as) []
	      _ -> MixfixType (f:as) 

anaType (LazyType t p) =
    do newT <- anaType t
       return $ LazyType newT p

anaType (ProductType ts ps) =
    do newTs <- mapM anaType ts
       return $ ProductType newTs ps

anaType (FunType t1 a t2 ps) =
    do newT1 <- anaType t1
       newT2 <- anaType t2
       return $ FunType newT1 a newT2 ps

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token (getBrackets k) [head ps, last ps] 

getBrackets :: BracketKind -> [String]
getBrackets k = 
    case k of Parens -> ["(", ")"]
	      Squares -> ["[", "]"]
	      Braces -> ["{", "}"]

