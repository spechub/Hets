
{- HetCATS/HasCASL/TypeAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse given classes and types
-}

module TypeAna where

import As
import AsUtils
import GlobalAnnotationsFunctions(emptyGlobalAnnos)
import Id
import Le
import List(nub)
import Maybe
import MonadState
import Pretty
import PrettyPrint
import PrintAs()
import FiniteMap
import Result

-- ---------------------------------------------------------------------------
-- analyse class
-- ---------------------------------------------------------------------------

anaClassName :: Bool -> ClassName -> State Env (Result [ClassName])
-- True: declare the class
anaClassName b ci = 
    do ce <- getClassEnv
       if isJust $ lookupFM ce ci then return $ return [ci]
	 else if b then 
		do putClassEnv $ defCEntry ce ci [] universe
                   return $ return [ci]
	      else 	  
		return $ plain_error [] 
		    ("undeclared class '" ++ tokStr ci ++  "'")
		    (tokPos ci)

anaClass :: Bool -> Class -> State Env Class
anaClass b c@(As.Intersection cs ps) = 
    if null cs
       then 
       do if null ps then return ()  -- no warning 
	    else appendDiags [Diag Warning
				 "redundant universe class" 
				 (head ps)]
	  return c
       else
    do Result ds (Just l) <- anaList (anaClassName (b && null (tail cs))) cs
       appendDiags ds
       return $ Intersection (nub $ concat l) ps

anaClass _ (Downset t) = 
    do newT <- anaType t
       return $ Downset newT

anaClassAppl :: Class -> State Env Class
anaClassAppl c = anaClass False c

-- ----------------------------------------------------------------------------
-- analyse kind
-- ----------------------------------------------------------------------------

anaKind :: Kind -> State Env Kind
anaKind (Kind args c p) = 
    do ca <- anaClassAppl c
       newArgs <- mapM anaProdClass args
       return $ Kind newArgs ca p

anaExtClass :: ExtClass -> State Env ExtClass
anaExtClass (ExtClass c v p) = 
    do ca <- anaClassAppl c
       return $ ExtClass ca v p
anaExtClass (KindArg k) =
    do n <- anaKind k
       return $ KindArg n

anaProdClass :: ProdClass -> State Env ProdClass
anaProdClass (ProdClass l p) =
    do cs <- mapM anaExtClass l
       return $ ProdClass cs p

-- ---------------------------------------------------------------------------
-- analyse type
-- ---------------------------------------------------------------------------

checkTypeKind :: Id -> Kind -> State Env [Diagnosis]
checkTypeKind i k = 
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> return [Diag Error 
		      ("unknown type '" ++ showId i "'")
				   (posOfId i)]
	   Just k2 -> if eqKind k2 k 
			  then return []
			  else return [Diag Error
				       ("incompatible type kinds\n" ++ 
					indent 2 (showPretty k . 
						  showChar '\n' .  
						  showPretty k2) "")
				   (posOfKind k)]

anaTypeId :: Id -> State Env Type
anaTypeId i = 
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> do
		      appendDiags [Diag Error 
				   ("unidentified type '" ++ showId i "'")
				   (posOfId i)]
		      return (TypeConstrAppl i 0 nullKind [] []) 
	   Just k -> return $ TypeConstrAppl i 0 k [] []

anaType :: Type -> State Env Type
anaType (t@(TypeConstrAppl i v k ts _)) =
    let e1 = if length ts > kindArity k then
	     [Diag Error ("too many type arguments:\n" ++
	       indent 2 (showPretty t) "")
	      (posOfType t)] else []
	e2 = if v > 0 then 
	     [Diag Error 
	      ("too many type arguments:\n" ++
	       indent 2 (showPretty t) "")
	      (posOfType t)] else []
    in do ds <- checkTypeKind i k
	  appendDiags $ e1 ++ e2 ++ ds
	  return t

anaType (TypeToken t) = 
    anaTypeId $ simpleIdToId t

anaType (BracketType Parens ts ps) =
    do newTs <- mapM anaType ts
       return $ ProductType newTs ps

anaType (BracketType b ts ps) =
    let toks@[o,c] = mkBracketToken b ps 
	i = if null ts then Id toks [] [] 
	    else Id [o, Token place $ posOfType $ head ts, c] [] []
    in
    do newT <- anaTypeId i
       if null ts then return newT
	  else do args <- mapM anaType ts
		  case newT of
			   TypeConstrAppl _ _ k _ _ -> 
			       do if kindArity k < length args then
				     appendDiags [Diag Error 
						  ("too many arguments for '"
						   ++ showId i "'")
						 $ posOfId i]
				     else return ()
				  return $ TypeConstrAppl i 0 k args []
			   _ -> return $ TypeConstrAppl i 0
				     (Kind 
				      [ProdClass 
				       (replicate (length args) extUniverse) 
				       [] ] universe []) args []

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
    if null ps then error "mkBracketToken"
       else zipWith Token (getBrackets k) [head ps, last ps] 

getBrackets :: BracketKind -> [String]
getBrackets k = 
    case k of Parens -> ["(", ")"]
	      Squares -> ["[", "]"]
	      Braces -> ["{", "}"]



-- --------------------------------------------------------------------------
showPretty :: PrettyPrint a => a -> ShowS
showPretty = showString . render . printText0 emptyGlobalAnnos 

posOfKind :: Kind -> Pos
posOfKind (Kind l c ps) = 
    if null l then posOfClass c
       else if null ps then posOfProdClass $ head l
	    else head ps

posOfProdClass :: ProdClass -> Pos
posOfProdClass (ProdClass s ps) = 
    if null s then if null ps then nullPos else head ps 
       else posOfExtClass $ head s

posOfExtClass :: ExtClass -> Pos
posOfExtClass (ExtClass c _ _) = posOfClass c
posOfExtClass (KindArg k) = posOfKind k

posOfClass :: Class -> Pos 
posOfClass (Downset t) = posOfType t
posOfClass (Intersection is ps) = 
    if null ps then if null is then nullPos else tokPos $ head is
       else head ps

eqKind :: Kind -> Kind -> Bool
eqKind (Kind p1 c1 _) (Kind p2 c2 _) =
    eqListBy eqProdClass p1 p2 && eqClass c1 c2

eqListBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqListBy _ [] [] = True
eqListBy f (h1:t1) (h2:t2) = f h1 h2 && eqListBy f t1 t2
eqListBy _ _ _ = False

eqProdClass :: ProdClass -> ProdClass -> Bool
eqProdClass (ProdClass s1 _) (ProdClass s2 _) =
    eqListBy eqExtClass s1 s2

eqExtClass :: ExtClass -> ExtClass -> Bool
eqExtClass (ExtClass c1 v1 _) (ExtClass c2 v2 _) = 
    eqClass c1 c2 && v1 == v2
eqExtClass (KindArg k1) (KindArg k2) = eqKind k1 k2
eqExtClass _ _ = False

eqClass :: Class -> Class -> Bool
eqClass(Intersection i1 _) (Intersection i2 _) = i1 == i2
eqClass (Downset t1) (Downset t2) = eqType t1 t2
eqClass _ _ = False

eqType :: Type -> Type -> Bool
eqType = error "eqType nyi"
