
{- HetCATS/HasCASL/TypeAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse types
-}

module TypeAna where

import As
import AsUtils
import GlobalAnnotationsFunctions(emptyGlobalAnnos)
import Id
import Le
import MonadState
import Pretty
import PrettyPrint
import PrintAs
import FiniteMap
import Result
import Set

checkTypeKind :: Id -> Kind -> Type -> State Env (Result Type)
checkTypeKind i k t = 
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> return $ plain_error t 
		      ("unknown type '" ++ showId i "'")
				   (posOfId i)
	   Just k2 -> if eqKind k2 k 
			  then return $ return t 
			  else return $ plain_error t
				       ("incompatible type kinds\n" ++ 
					indent 2 (showPretty k . 
						  showChar '\n' .  
						  showPretty k2) "")
				   (posOfKind k)

anaType :: Type -> State Env (Result Type)
anaType (t@(TypeConstrAppl i k ts _)) =
    if length ts > kindArity k then
       return $ plain_error t 
	      ("too many type arguments:\n" ++
	       indent 2 (showPretty t) "")
	      (posOfType t)
       else checkTypeKind i k t

anaType (t@(TypeVar i k v _)) =
	 if v > 0 then return $ plain_error t
	               ("unexpected generic variable '" ++ showId i "i")
	               (posOfId i)
	 else checkTypeKind i k t

anaType (TypeToken t) = 
    let i = simpleIdToId t in
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> return $ plain_error (TypeToken t) 
		      ("unidentified type token '" ++ tokStr t)
		      (tokPos t)
	   Just k -> do ts <- getTypeVars 
			return $ return $ if i `elementOf` ts
			       then TypeVar i k 0 []
			       else TypeConstrAppl i k [] []

anaType (BracketType Parens ts ps) =
    do Result ds (Just newTs) <- anaList anaType ts
       return $ Result ds $ Just $ ProductType newTs ps

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
posOfExtClass (KindAppl k _) = posOfKind k

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
eqExtClass (KindAppl f1 a1) (KindAppl f2 a2) =
    eqKind f1 f2 && eqKind a1 a2
eqExtClass _ _ = False

eqClass :: Class -> Class -> Bool
eqClass(Intersection i1 _) (Intersection i2 _) =
    i1 == i2
eqClass (Downset t1) (Downset t2) = eqType t1 t2
eqClass _ _ = False

eqType :: Type -> Type -> Bool
eqType = error "eqType nyi"
