
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
import List
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

-- transitiv super classes 
-- PRE: all superclasses and defns must be defined in ClassEnv
-- and there must be no cycle!
allSuperClasses :: ClassMap -> ClassId -> [ClassId]
allSuperClasses ce ci = 
    let recurse = nub . concatMap (allSuperClasses ce) in
    case lookupFM ce ci of 
    Just info -> nub $ (case classDefn info of 
			Nothing -> [ci]
			Just (Intersection cis _) -> recurse cis
			Just _ -> [ci])
		 ++ recurse (superClasses info)
    Nothing -> error "allSuperClasses"

resolveClassSyn :: ClassMap -> ClassId -> [ClassId]
resolveClassSyn cMap ci = 
    case lookupFM cMap ci of 
    Nothing -> error "resolveClassSyn"
    Just info -> case classDefn info of 
		      Nothing -> [ci]
		      Just (Intersection cis _) -> resolveClassSyns cMap cis
		      Just _ -> [ci]

-- downsets should be expanded to a unique type string

resolveClassSyns :: ClassMap -> [ClassId] -> [ClassId]
resolveClassSyns cSyns cis = nub $ 
			      concatMap (resolveClassSyn cSyns) cis

anaClassId :: ClassMap -> ClassId -> [Diagnosis]
-- True: declare the class
anaClassId cMap ci = 
       if isJust $ lookupFM cMap ci then []
	      else [Diag Error 
		    ("undeclared class '" ++ showId ci "'")
		    $ posOfId ci]

anaClass :: Class -> State Env Class
anaClass (Intersection cs ps) = 
    do cMap <- getClassMap
       let l = zip (map (anaClassId cMap) cs) cs
	   restCs = map snd $ filter (\ (x, _) -> null x) l  
	   ds = concatMap fst l 
       appendDiags ds 
       return $ Intersection restCs ps 

anaClass (Downset t) = 
    do newT <- anaType t
       return $ Downset newT

-- ----------------------------------------------------------------------------
-- analyse kind
-- ----------------------------------------------------------------------------

anaKind :: Kind -> State Env Kind
anaKind (Kind args c p) = 
    do ca <- anaClass c
       newArgs <- mapM anaProdClass args
       return $ Kind newArgs ca p

anaExtClass :: ExtClass -> State Env ExtClass
anaExtClass (ExtClass c v p) = 
    do ca <- anaClass c
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

eqKindDiag :: Kind -> Kind -> [Diagnosis]
eqKindDiag k1 k2 = 
    if eqKind Compatible k1 k2 then []
       else [ Diag Error
	      ("incompatible kinds\n" ++ 
	       indent 2 (showPretty k1 . 
			 showChar '\n' .  
			 showPretty k2) "")
	    $ posOfKind k1 ]

checkTypeKind :: Id -> Kind -> State Env [Diagnosis]
checkTypeKind i k = 
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> return [Diag Error 
		      ("unknown type '" ++ showId i "'")
				   (posOfId i)]
	   Just ks -> return $ eqKindDiag k $ head ks

indent :: Int -> ShowS -> ShowS
indent i s = showString $ concat $ 
	     intersperse ('\n' : replicate i ' ') (lines $ s "")

anaTypeId :: Id -> State Env Type
anaTypeId i = 
    do tk <- getTypeKinds
       case lookupFM tk i of
           Nothing -> do
		      appendDiags [Diag Error 
				   ("undeclared type '" ++ showId i "'")
				   (posOfId i)]
		      return (TypeConstrAppl i 0 nullKind [] []) 
	   Just ks -> return $ TypeConstrAppl i 0 (head ks) [] []

anaType :: Type -> State Env Type
anaType (t@(TypeConstrAppl i v k ts _)) = do
    let e1 = if length ts > kindArity k then
	     [Diag Error ("too many type arguments:\n" ++
	       indent 2 (showPretty t) "")
	      (posOfType t)] else []
	e2 = if v > 0 then 
	     [Diag Error 
	      ("uninstantiated generic variable " ++
	       showId i "")
	      (posOfId i)] else []
    ds <- checkTypeKind i k
    appendDiags $ e1 ++ e2 ++ ds
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
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token (getBrackets k) [head ps, last ps] 

getBrackets :: BracketKind -> [String]
getBrackets k = 
    case k of Parens -> ["(", ")"]
	      Squares -> ["[", "]"]
	      Braces -> ["{", "}"]

-- --------------------------------------------------------------------------
showPretty :: PrettyPrint a => a -> ShowS
showPretty = showString . render . printText0 emptyGlobalAnnos 

missingAna :: PrettyPrint a => a -> [Pos] -> State Env ()
missingAna t ps = appendDiags [Diag FatalError 
			       ("no analysis yet for: " ++ showPretty t "")
			      $ if null ps then nullPos else head ps]

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
    if null ps then if null is then nullPos else posOfId $ head is
       else head ps

data EqMode = Compatible | SameSyntax

eqKind :: EqMode -> Kind -> Kind -> Bool
eqKind emod (Kind p1 c1 _) (Kind p2 c2 _) =
    eqListBy (eqProdClass emod) p1 p2 && 
    case emod of Compatible -> True
		 SameSyntax -> eqClass c1 c2

eqListBy :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqListBy _ [] [] = True
eqListBy f (h1:t1) (h2:t2) = f h1 h2 && eqListBy f t1 t2
eqListBy _ _ _ = False

eqProdClass :: EqMode -> ProdClass -> ProdClass -> Bool
eqProdClass emod (ProdClass s1 _) (ProdClass s2 _) =
    eqListBy (eqExtClass emod) s1 s2

eqExtClass :: EqMode -> ExtClass -> ExtClass -> Bool
eqExtClass emod (ExtClass c1 v1 _) (ExtClass c2 v2 _) = 
    case emod of Compatible -> True
		 SameSyntax -> eqClass c1 c2 && v1 == v2
eqExtClass emod (KindArg k1) (KindArg k2) = eqKind emod k1 k2
eqExtClass _ _ _ = False

eqClass :: Class -> Class -> Bool
eqClass(Intersection i1 _) (Intersection i2 _) = i1 == i2
eqClass (Downset t1) (Downset t2) = t1 == t2
eqClass _ _ = False

