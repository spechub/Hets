{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
Morphism on 'Env' (as for CASL)
-}

module HasCASL.Morphism where

import HasCASL.Le
import HasCASL.HToken
import HasCASL.As
import HasCASL.AsToLe
import HasCASL.PrintAs
import HasCASL.PrintLe
import HasCASL.Unify
import HasCASL.Merge
import HasCASL.Symbol
import Common.Id
import Common.Keywords
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Lib.State
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Data.List(partition)

-- new type to defined a different Eq and Ord instance
data TySc = TySc TypeScheme deriving Show

instance Eq TySc where
    TySc sc1 == TySc sc2 = 
	let Result _ ms = mergeScheme Map.empty 0 sc1 sc2 
	    in maybe False (const True) ms

instance Ord TySc where
-- this does not match with Eq TypeScheme!
    TySc sc1 <= TySc sc2 = 
	TySc sc1 == TySc sc2 || 
	         let (t1, c) = runState (freshInst sc1) 1
		     t2 = evalState (freshInst sc2) c
		     v1 = varsOf t1
		     v2 = varsOf t2
                 in case compare (Set.size v1) $ Set.size v2 of 
			LT -> True
			EQ -> t1 <= subst (Map.fromAscList $
			    zipWith (\ v (TypeArg i k _ _) ->
				     (v, TypeName i k 1)) 
					   (Set.toList v1) $ Set.toList v2) t2
			GT -> False 		   

data SymbolType = OpAsItemType TySc
		| TypeAsItemType Kind
		| ClassAsItemType Kind
		  deriving (Show, Eq, Ord)

instance PrettyPrint SymbolType where
    printText0 ga t = case t of 
      OpAsItemType (TySc sc) -> printText0 ga sc
      TypeAsItemType k -> printText0 ga k
      ClassAsItemType k -> printText0 ga k

data Symbol = Symbol {symName :: Id, symbType :: SymbolType} 
	      deriving (Show, Eq, Ord)

data RawSymbol = ASymbol Symbol | AnID Id | AKindedId SymbKind Id
    	         deriving (Show, Eq, Ord)

type SymbolMap = Map.Map Symbol Symbol 
type RawSymbolMap = Map.Map RawSymbol RawSymbol
type SymbolSet = Set.Set Symbol 

idToTypeSymbol :: Id -> Kind -> Symbol
idToTypeSymbol idt k = Symbol idt $ TypeAsItemType k

idToClassSymbol :: Id -> Kind -> Symbol
idToClassSymbol idt k = Symbol idt $ ClassAsItemType k

idToOpSymbol :: Id -> TySc -> Symbol
idToOpSymbol idt typ = Symbol idt $ OpAsItemType typ

idToRaw :: Id -> RawSymbol
idToRaw x = AnID x

rawSymName :: RawSymbol -> Id
rawSymName (ASymbol sym) = symName sym
rawSymName (AnID i) = i
rawSymName (AKindedId _ i) = i

symbTypeToKind :: SymbolType -> SymbKind
symbTypeToKind (OpAsItemType _)    = SK_op
symbTypeToKind (TypeAsItemType _)  = SK_type
symbTypeToKind (ClassAsItemType _) = SK_class

symbolToRaw :: Symbol -> RawSymbol
symbolToRaw sym = ASymbol sym

symOf :: Env -> SymbolSet
symOf sigma = 
    let classes = Map.foldWithKey ( \ i ks s -> 
			Set.insert (Symbol i $ ClassAsItemType $
				    Intersection (classKinds ks) []) s) 
		  Set.empty $ classMap sigma
	types = Map.foldWithKey ( \ i ti s -> 
			Set.insert (Symbol i $ TypeAsItemType $
				    typeKind ti) s) 
		classes $ typeMap sigma
        ops = Map.foldWithKey ( \ i ts s0 ->
		      foldr ( \ t s1 -> 
			  Set.insert (Symbol i $ OpAsItemType $ TySc $
				      opType t) s1) s0 $ opInfos ts)
	      types $ assumps sigma
	in ops

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
	let r = return $ ASymbol $ idToOpSymbol idt (TySc sc)
	    rk = if null vs then Nothing else 
		 convertTypeToKind t 
	    rrk = maybeToResult (getMyPos t) 
	                   ("not a kind: " ++ showPretty t "") rk
	in case k of 
	      SK_op -> r
	      SK_fun -> r
	      SK_pred -> return $ ASymbol $ idToOpSymbol idt $ 
			 TySc $ predTypeScheme sc
	      SK_class -> do ck <- rrk
			     return $ ASymbol $ idToClassSymbol idt ck
	      _ -> do ck <- rrk
		      return $ ASymbol $ idToTypeSymbol idt ck

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
matchSymb x                               (ASymbol y)            =  x==y
matchSymb (Symbol idt _)                  (AnID di)              = idt==di
matchSymb (Symbol idt (OpAsItemType _))   (AKindedId SK_op di)   = idt==di
matchSymb (Symbol idt (OpAsItemType _))   (AKindedId SK_fun di)  = idt==di
matchSymb (Symbol idt (OpAsItemType _))   (AKindedId SK_pred di) = idt==di
matchSymb (Symbol idt (TypeAsItemType _)) (AKindedId SK_type di) = idt==di
matchSymb (Symbol idt (TypeAsItemType _)) (AKindedId SK_sort di) = idt==di
matchSymb (Symbol idt (ClassAsItemType _))(AKindedId SK_class di)= idt==di
matchSymb _                               _                      = False

type IdMap = Map.Map Id Id

mapType :: IdMap -> Type -> Type
-- include classIdMap later
mapType m t = case t of
	   TypeName i k n ->
	       if n == 0 then 
		  case Map.lookup i m of
		  Just j -> TypeName j k 0
		  _ -> t
	       else t
	   TypeAppl t1 t2 ->
	       TypeAppl (mapType m t1) (mapType m t2)
	   TypeToken _ -> t
	   BracketType b l ps ->
	       BracketType b (map (mapType m) l) ps
	   KindedType tk k ps -> 
	       KindedType (mapType m tk) k ps
	   MixfixType l -> MixfixType $ map (mapType m) l
	   LazyType tl ps -> LazyType (mapType m tl) ps
	   ProductType l ps -> ProductType (map (mapType m) l) ps
           FunType t1 a t2 ps -> FunType (mapType m t1) a (mapType m t2) ps

mapTypeScheme :: IdMap -> TypeScheme -> TypeScheme
-- rename clashing type arguments later
mapTypeScheme m (TypeScheme args (q :=> t) ps) =
    TypeScheme args (q :=> mapType m t) ps

mapTySc :: IdMap -> TySc -> TySc
mapTySc m (TySc s1) = TySc (mapTypeScheme m s1)


type FunMap = Map.Map (Id, TySc) (Id, TySc)

mapFunSym :: IdMap -> FunMap -> (Id, TySc) -> Maybe (Id, TySc)
mapFunSym tm fm (i, sc) = do
  (newI, _sc1) <- Map.lookup (i, sc) fm
  let sc2 = mapTySc tm sc
      -- unify sc2 with sc1 later
  return (newI, sc2)

mergeOpInfos :: TypeMap -> Int -> OpInfos -> OpInfos -> Result OpInfos 
mergeOpInfos tm c (OpInfos l1) (OpInfos l2) = 
    do l <- mergeOps tm c l1 l2
       return $ OpInfos l
-- trace (showPretty l1 "\n+ " ++ showPretty l2 "\n 0" ++ showPretty l "") l

mergeOps :: TypeMap -> Int -> [OpInfo] -> [OpInfo] -> Result [OpInfo]
mergeOps _ _ [] l = return l
mergeOps tm c (o:os) l2 = do 
    let (es, us) = partition (isUnifiable tm c (opType o) . opType) l2
    l1 <- mergeOps tm c os us 
    if null es then return (o : l1)
       else do r <- mergeOpInfo tm c o $ head es
	       return (r : l1)

mergeEnv :: Env -> Env -> Result Env
mergeEnv e1 e2 =
	do cMap <- merge (classMap e1) $ classMap e2
	   let m = max (counter e1) $ counter e2
	   tMap <- mergeMap (mergeTypeInfo Map.empty 0) 
		   (typeMap e1) $ typeMap e2
	   as <- mergeMap (mergeOpInfos tMap m) 
		 (assumps e1) $ assumps e2
	   return initialEnv { classMap = cMap
			     , typeMap = tMap
			     , assumps = as }

data Morphism = Morphism { msource :: Env
			 , mtarget :: Env
			 , classIdMap :: IdMap  -- ignore
			 , typeIdMap :: IdMap 
                         , funMap :: FunMap } 
                         deriving (Eq, Show)

mkMorphism :: Env -> Env -> Morphism
mkMorphism e1 e2 = Morphism e1 e2 Map.empty Map.empty Map.empty

embedMorphism :: Env -> Env -> Morphism
embedMorphism a b =
    (mkMorphism a b) 
    { typeIdMap = foldr (\x -> Map.insert x x) Map.empty 
                $ Map.keys $ typeMap a
    , funMap = Map.foldWithKey 
                 ( \ i (OpInfos ts) m -> foldr 
                      (\ oi -> let v = (i, TySc $ opType oi) in 
		           Map.insert v v) m ts)
                 Map.empty $ assumps a
    }

ideMor :: Env -> Morphism
ideMor e = embedMorphism e e

compMor :: Morphism -> Morphism -> Maybe Morphism
compMor m1 m2 = 
  if isSubEnv (mtarget m1) (msource m2) then Just 
      (mkMorphism (msource m1) (mtarget m2))
      { typeIdMap = Map.map ( \ i -> Map.findWithDefault i i $ typeIdMap m2)
			     $ typeIdMap m1 
      , funMap = Map.foldWithKey ( \ (i1, sc1) (i2, sc2) m -> 
		       Map.insert (i1, sc1) 
		       (Map.findWithDefault (i2, sc2) (i2, sc2) $ 
			funMap m2) m) Map.empty $ funMap m1
      }
   else Nothing

inclusionMor :: Env -> Env -> Result Morphism
inclusionMor e1 e2 =
  if isSubEnv e1 e2
     then return (embedMorphism e1 e2)
     else pplain_error (ideMor initialEnv)
          (ptext "Attempt to construct inclusion between non-subsignatures:"
           $$ ptext "Singature 1:" $$ printText e1
           $$ ptext "Singature 2:" $$ printText e2)
           nullPos

symbMapToMorphism :: Env -> Env -> SymbolMap -> Result Morphism
symbMapToMorphism sigma1 sigma2 smap = do
  type_map1 <- Map.foldWithKey myIdMap (return Map.empty) $ typeMap sigma1
  fun_map1 <- Map.foldWithKey myAsMap (return Map.empty) $ assumps sigma1
  return (mkMorphism sigma1 sigma2)
	 { typeIdMap = type_map1
	 , funMap = fun_map1}
  where
  myIdMap i k m = do
    m1 <- m 
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map sort "++showId i "")
             $ Map.lookup (Symbol { symName = i
				  , symbType = TypeAsItemType 
				               $ typeKind k}) smap
    return (Map.insert i (symName sym) m1)
  myAsMap i (OpInfos ots) m = foldr (insFun i) m ots
  insFun i ot m = do
    let osc = TySc $ opType ot
    m1 <- m
    sym <- maybeToResult nullPos 
             ("symbMapToMorphism - Could not map op "++showId i "")
             $ Map.lookup (Symbol { symName = i
				  , symbType = OpAsItemType osc}) smap
    k <- case symbType sym of
        OpAsItemType sc -> return sc
        _ -> plain_error osc
              ("symbMapToMorphism - Wrong result symbol type for op"
               ++showId i "") nullPos 
    return (Map.insert (i, osc) (symName sym,k) m1)

legalEnv :: Env -> Bool
legalEnv _ = True -- maybe a closure test?
legalMor :: Morphism -> Bool
legalMor m = let s = msource m
		 t = mtarget m
		 ts = typeIdMap m
		 fs = funMap m
	     in  
	     all (`elem` (Map.keys $ typeMap s)) 
		  (Map.keys ts)
	     && all (`elem` (Map.keys $ typeMap t))
		(Map.elems ts)
	     && all ((`elem` (Map.keys $ assumps s)) . fst)
		(Map.keys fs)
	     && all ((`elem` (Map.keys $ assumps t)) . fst)
		(Map.elems fs)

morphismUnion :: Morphism -> Morphism -> Result Morphism
morphismUnion m1 m2 = 
    do s <- mergeEnv (msource m1) $ msource m2
       t <- mergeEnv (mtarget m1) $ mtarget m2
       tm <- foldr ( \ (i, j) rm -> 
		     do m <- rm
		        case Map.lookup i m of
		          Nothing -> return $ Map.insert i j m
		          Just k -> if j == k then return m
		            else do 
		            Result [Diag Error 
			      ("incompatible mapping of type id: " ++ 
			       showId i " to: " ++ showId j " and: " 
			       ++ showId k "") $ posOfId i] $ Just ()
		            return m) 
	     (return $ typeIdMap m1) $ Map.toList $ typeIdMap m2
       fm <- foldr ( \ (isc@(i, _), jsc@(j, TySc sc1)) rm -> do
		     m <- rm
		     case Map.lookup isc m of
		       Nothing -> return $ Map.insert isc jsc m
		       Just ksc@(k, TySc sc2) -> if j == k && 
		         isUnifiable (typeMap t) 0 sc1 sc2  
		         then return m
		            else do 
		            Result [Diag Error 
			      ("incompatible mapping of op: " ++ 
			       showFun isc " to: " ++ showFun jsc " and: " 
			       ++ showFun ksc "") $ posOfId i] $ Just ()
		            return m) 
	     (return $ funMap m1) $ Map.toList $ funMap m2
       return (mkMorphism s t) 
		  { typeIdMap = tm
		  , funMap = fm }

showFun :: (Id, TySc) -> ShowS
showFun (i, TySc ty) = showId i . (" : " ++) . showPretty ty

morphismToSymbMap :: Morphism -> SymbolMap
morphismToSymbMap mor = 
  let
    tm = typeMap $ msource mor 
    typeSymMap = 
      Map.foldWithKey
         ( \ s1 s2 m -> let k = typeKind $ 
	                        Map.findWithDefault starTypeInfo s1 tm 
	   in Map.insert (idToTypeSymbol s1 k) (idToTypeSymbol s2 k) m)
         Map.empty $ 
         typeIdMap mor
   in Map.foldWithKey
         ( \ (id1,t1) (id2,t2) m -> 
             Map.insert (idToOpSymbol id1 t1) 
                        (idToOpSymbol id2 t2) m)
         typeSymMap $ funMap mor 

instance PrettyPrint Morphism where
  printText0 ga m = braces (printText0 ga (msource m)) 
		    $$ text mapsTo
		    <+> braces (printText0 ga (mtarget m))

instance PrettyPrint Symbol where
  printText0 ga s = text (case symbType s of 
			  OpAsItemType _ -> opS
			  TypeAsItemType _ -> typeS
			  ClassAsItemType _ -> classS) <+> 
                    printText0 ga (symName s) <+> text colonS <+> 
		    printText0 ga (symbType s)

instance PrettyPrint RawSymbol where
  printText0 ga rs = case rs of
      ASymbol s -> printText0 ga s
      AnID i -> printText0 ga i
      AKindedId k i -> text (case k of 
           SK_type -> typeS
           SK_sort -> sortS			     
           SK_op -> opS 
	   SK_fun -> funS
	   SK_pred -> predS
           SK_class -> classS
	   Implicit -> "") <+> printText0 ga i
