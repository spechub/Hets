{- 
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Coding out subsorting into unary predicates.
   New concept for proving Ontologies.
-}

{-
   todo:

-}

module Comorphisms.CASL2TopSort where

import Control.Exception (assert)
import Debug.Trace (trace)
import Maybe

import Logic.Logic
import Logic.Comorphism
import Common.Id
import Common.Result
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation

-- CASL
import CASL.Logic_CASL 
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism 
import CASL.Sublogic
import CASL.Utils
import CASL.Overload (injName)
-- import List (nub,delete)
-- import Common.ListUtils
-- import Data.List

-- | The identity of the comorphism
data CASL2TopSort = CASL2TopSort deriving (Show)

instance Language CASL2TopSort -- default definition is okay

instance Comorphism CASL2TopSort
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol ()
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               Symbol RawSymbol () where
    sourceLogic CASL2TopSort = CASL
    sourceSublogic CASL2TopSort = CASL_SL
                      { has_sub = True,
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2TopSort = CASL
    targetSublogic CASL2TopSort = CASL_SL
                      { has_sub = False, -- subsorting is coded out
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    map_sign CASL2TopSort = transSig
    map_morphism CASL2TopSort mor = 
        let rsigSour = trSig $ msource mor
            rsigTarg = trSig $ mtarget mor
        in case rsigSour of
           Result diags1 mrs ->
               case rsigTarg of
               Result diags2 mrt 
                  | isJust mrs && isJust mrt ->
                      Result (diags1++diags2) (Just 
                               (mor { msource = fromJust mrs
                                    , mtarget = fromJust mrt }))
                      
                  | otherwise -> 
                     (Result (diags1++diags2) Nothing)
      where trSig sig = case transSig sig of
                        Result dias mr -> 
                            Result dias (maybe Nothing
                                                (Just . fst)
                                                mr)
    map_sentence CASL2TopSort = transSen
    map_symbol CASL2TopSort = Set.single . id


data PredInfo = PredInfo { topSort_PI    :: SORT
			 , directSuperSorts_PI :: Set.Set SORT
			 , predicate_PI  :: PRED_NAME
			 } deriving (Show,Ord,Eq)

type SubSortMap = Map.Map SORT PredInfo

generateSubSortMap :: Set.Set SORT -> Rel.Rel SORT 
                   -> Map.Map Id (Set.Set PredType) 
		   -> Result SubSortMap
generateSubSortMap sorSet sortRels pMap = 
    let sortRelsMap = Rel.toMap sortRels
	initPI p set s = PredInfo { topSort_PI = s
				  , directSuperSorts_PI = set
				  , predicate_PI = p } 
	checkSet k s = case s `Set.difference`
		          (Set.fromAscList $ Map.keys sortRelsMap) of
		       ds | Set.size ds == 1 -> 
			      let ts = head $ Set.toList ds
		               in Right $ initPI k (filterTrans k s ts) ts
			  | otherwise        -> Left ds
	filterTrans k set ts =
	    let preSuperSorts = Set.unions $ 
		         map (\ s -> maybe Set.empty id 
			                   (Map.lookup s sortRelsMap)) $
			 Set.toList $ 
			 Set.filter (\ s -> not (Rel.member s k sortRels)) $
			 Set.delete k $ set
		resSRel = Rel.restrict sortRels
		pSupSl = Set.toList preSuperSorts
		pairSets = [Set.fromList [x,y] | x <- pSupSl, 
			                         y <- pSupSl, 
			                         x/=y, x<y]
		isos = Set.unions $ map (\p -> if Set.size (Rel.toSet $ 
							    resSRel p) == 4
					       then p
                                               else Set.empty) pairSets 
		superSorts = preSuperSorts `Set.difference` isos 
	    in Set.delete ts $ 
	       Set.delete k (set `Set.difference` superSorts)
	initMap = Map.mapWithKey checkSet sortRelsMap 
	grepRight k v nm = case v of
			   Right v1  -> Map.insert k v1 nm
			   Left ds   
			       | Set.size ds > 1 -> 
				   error ("Comorphism.CASL2TopSort."++
					  "generateSubSortMap: " ++ 
					  show k++" has more than"++
					  " one maximal Supersort: "++
					  show ds++"!")
			       | otherwise -> nm
	leftNonEmpty x = case x of
			 Left ds -> Set.size ds > 1 -- ==1 is checked above
			 _ -> False
	disAmbMap m  = Map.map disAmbPred m
	disAmbPred v = if (predicate_PI v) `Map.member` pMap
		       then disAmbPred' (1::Int) v'
		       else v
	    where v' = add "_s" v
		  disAmbPred' x v1 = 
		      if (predicate_PI v1) `Map.member` pMap
		      then disAmbPred' (x+1) (add (show x) v')
		      else v1
		  add s v1 = v1 {predicate_PI = 
                                   case predicate_PI v1 of
				   Id ts is ps -> 
				      assert (not $ null ts) $
				          Id (init ts ++ 
					      [(last ts) {tokStr = 
							  tokStr (last ts)++s}
					      ]) is ps
				}
	allSorts m = let ks = Set.fromAscList $ Map.keys m
	             in ks `Set.union` Set.image topSort_PI (Map.image m ks) 
	                 == sorSet
    in -- trace (show initMap) $
       if not $ null $ filter leftNonEmpty $ Map.elems initMap
       then Result [] Nothing
       else case Map.foldWithKey grepRight Map.empty initMap of
            m | Map.isEmpty m    -> Result [] Nothing
	      | not (allSorts m) -> Result [Diag Warning "CASL2TopSort: not all sorts had a maximal supersort" nullPos] Nothing 
	      | otherwise        -> Result [] $ Just $ disAmbMap m
    

-- | Finds Top-sort(s) and transforms for each top-sort all subsorts
-- into unary predicates. All predicates typed with subsorts are now
-- typed with the top-sort and axioms reflecting the typing are
-- generated. The operations are treated analogous. Axioms are
-- generated that each generated unary predicate must hold on at least
-- one element of the top-sort.

transSig :: Sign f e -> Result (Sign f e,[Named (FORMULA f)])
transSig sig = 
    case generateSubSortMap (sortSet sig) (sortRel sig) (predMap sig) of
    Result dias m_subSortMap ->
      maybe (Result dias Nothing)
            (\ subSortMap -> 
               let (dias2,newPredMap) = 
                       Map.mapAccum (\ds (un,ds1) -> (ds++ds1,un)) [] $
                       Map.unionWithKey repError 
		              (transPredMap subSortMap (predMap sig)) 
		              (newPreds subSortMap)
                   (Result dias3 maxioms) =
                       generateAxioms subSortMap (predMap sig) (opMap sig)
                   dias' = dias ++ dias2 ++ dias3
               in maybe (Result dias' Nothing)
                        (\axs -> Result dias' $ Just $
                   (sig { sortSet = Set.fromList $ 
		                    map topSort_PI $ Map.elems subSortMap
		        , sortRel = Rel.fromList []
		        , opMap   = transOpMap subSortMap (opMap sig)
		        , assocOps= transOpMap subSortMap (assocOps sig)
		        , predMap = newPredMap
		        },axs))
                   maxioms)
          m_subSortMap          
    where 
	  repError k (v1,d1) (v2,d2) = 
              (Set.union v1 v2, 
               (Diag Warning
                     ("CASL2TopSort.transSig: generating "++
		      "overloading: Predicate "++show k++
		      " gets additional type(s): "++show v2) nullPos)
               :d1++d2 )   
	  newPreds mp = 
	      foldr (\ pI nm -> Map.insert (predicate_PI pI) 
		                           (Set.single  
					    (PredType [topSort_PI pI]),[]) nm)
	            Map.empty (Map.elems mp)


transPredMap :: SubSortMap -> Map.Map PRED_NAME (Set.Set PredType) 
	     -> Map.Map PRED_NAME (Set.Set PredType,[Diagnosis])
transPredMap subSortMap = Map.map (\s -> (Set.image transType s,[]))
    where transType t = t { predArgs = map (\s -> maybe s topSort_PI 
					          (Map.lookup s subSortMap))
			                   (predArgs t)}

transOpMap :: SubSortMap -> Map.Map OP_NAME (Set.Set OpType) 
	   -> Map.Map OP_NAME (Set.Set OpType)
transOpMap subSortMap = Map.map (tidySet . Set.image transType)
    where tidySet s = Set.fold joinPartial s s
            where joinPartial t@(OpType {opKind = Partial})  
                      | t {opKind = Total} `Set.member` s = Set.delete t
                      | otherwise                         = id
                  joinPartial _ = id
          transType t = 
	      t { opArgs = map lkp (opArgs t)
		, opRes = lkp (opRes t)}
	  lkp = (\s -> maybe s topSort_PI (Map.lookup s subSortMap))

procOpMapping :: SubSortMap 
              -> OP_NAME -> Set.Set OpType 
              -> Result [Named (FORMULA f)] -> Result [Named (FORMULA f)]
procOpMapping subSortMap opName set r@(Result ds1 mal) =
    case mkProfMapOp opName subSortMap set of
    Result ds2 (Just profMap) ->
        -- trace (show profMap) 
        (maybe r 
	       (\al -> 
                    Result (ds1++ds2)
                           (Just (al ++ Map.foldWithKey 
                                      procProfMapOpMapping
                                    [] profMap))) mal)
    Result ds2 Nothing -> Result (ds1++ds2) Nothing
  where 
     procProfMapOpMapping :: [SORT] -> (FunKind,Set.Set [Maybe PRED_NAME])
                             -> [Named (FORMULA f)] -> [Named (FORMULA f)]
     procProfMapOpMapping sl (kind,spl) =  
            genArgRest 
                 (genSenName "o" opName (length sl))
                 (genOpEquation kind opName)
                 sl spl

generateAxioms :: SubSortMap -> Map.Map PRED_NAME (Set.Set PredType) 
               -> Map.Map OP_NAME (Set.Set OpType) 
	       -> Result [Named (FORMULA f)]
generateAxioms subSortMap pMap oMap = 
    -- generate argument restrictions for operations
    case Map.foldWithKey (procOpMapping subSortMap) (return []) oMap of 
    Result dias m_opAxs -> maybe (Result dias Nothing) 
                                 (\axs -> -- trace (show dias) $
                                          Result dias 
                                     (Just (reverse hi_axs ++ 
                                            reverse p_axs ++ 
                                            reverse axs)))
                                 m_opAxs                                 
    where p_axs =
          -- generate argument restrictions for predicates
           Map.foldWithKey (\ pName set al ->
              case mkProfMapPred subSortMap set of
              profMap ->
                    -- trace (show profMap) 
		          (al ++ Map.foldWithKey 
                             (\sl -> genArgRest 
                                      (genSenName "p" pName (length sl))
                                      (genPredication pName) 
                                      sl) 
                                    [] profMap)) 
                   [] pMap
          hi_axs =
          -- generate subclass_of axioms derived from subsorts
          -- and non-emptyness axioms
              Map.fold (\ (PredInfo { topSort_PI = ts
			 , predicate_PI = subS
			 , directSuperSorts_PI = set
			 }) al -> 
               let supPreds = 
	             map (\ s -> 
                            maybe (error ("CASL2TopSort: genAxioms:"++
				   " impossible happend: "++show s)) 
			          predicate_PI (Map.lookup s subSortMap))  
                         (Set.toList set)
	           x = mkSimpleId "x" 
	        in al ++ zipWith (\sen supS -> sen { senName = show subS++
						               senName sen++
						               show supS })
	                 (concat [inlineAxioms CASL 
				  "sort ts\n\
				  \pred subS,supS: ts\n\
				  \ forall x : ts . subS(x) =>\n\
				  \ supS(x) %(_subclassOf_)%"|supS<-supPreds] 
			 ) supPreds ++
                         map (\sen -> sen { senName = show subS ++ 
                                                      senName sen}) 
                                 (concat [inlineAxioms CASL
                                  "sort ts\n\
                                  \pred subS: ts \n\
                                  \. exists x:ts . \n\
                                  \ subS(x) %(_non_empty)%"])
	     ) [] subSortMap
 
mkProfMapPred :: SubSortMap -> Set.Set PredType 
              -> Map.Map [SORT] (Set.Set [Maybe PRED_NAME])
mkProfMapPred ssm = Set.fold seperate Map.empty
    where seperate pt = Map.setInsert (pt2topSorts pt) (pt2preds pt) 
          pt2topSorts = map (lkupTop ssm) . predArgs
          pt2preds = map (lkupPRED_NAME ssm) . predArgs

mkProfMapOp :: OP_NAME -> SubSortMap -> Set.Set OpType 
              -> Result (Map.Map [SORT] (FunKind,Set.Set [Maybe PRED_NAME]))
mkProfMapOp opName ssm = Set.fold seperate (return Map.empty)
    where seperate ot r@(Result dias mmap) =
              maybe r  
                (\ mp -> Result dias' 
                              (Just 
                                (Map.insertWith (\ (k1,s1) (k2,s2) ->
                                           (min k1 k2,Set.union s1 s2)) 
                                        (pt2topSorts joinedList) 
                                        (fKind,
                                         Set.single (pt2preds joinedList)) 
                                        mp)))
                 mmap
              where joinedList = opArgs ot ++ [opRes ot]
                    fKind = opKind ot
                    dias' = if fKind == Partial 
                             then dias ++ 
                                  [Diag Warning 
                                        ("Please, check if operation \""++
                                         show opName ++ 
                                         "\" is still partial as intended,\
                                          \ since a joining of types could\
                                         \ have made it total!!")
                                        nullPos]
                             else dias
          pt2topSorts = map (lkupTop ssm) 
          pt2preds = map (lkupPRED_NAME ssm) 

lkupTop :: SubSortMap -> SORT -> SORT
lkupTop ssm s = maybe s topSort_PI (Map.lookup s ssm)

lkupPRED_NAME :: SubSortMap -> SORT -> Maybe PRED_NAME
lkupPRED_NAME ssm s = 
    maybe Nothing (Just . predicate_PI) (Map.lookup s ssm)

genArgRest :: String               
           -> ([SORT] -> [TERM f] -> FORMULA f) 
               -- ^ generates from a list of variables 
               -- either the predication or function equation
           -> [SORT] -> (Set.Set [Maybe PRED_NAME]) 
	   -> [Named (FORMULA f)] -> [Named (FORMULA f)]
genArgRest sen_name genProp sl spl fs = 
    let vars = genVars sl 
        mquant = genQuantification (genProp sl (map toSortTerm vars))
                                   vars spl 
    in
    fs ++ 
    maybe [] (\quant -> 
                  [NamedSen { senName  = sen_name
                            , sentence = quant}])
             mquant

-- | generate a predication with qualified pred name
genPredication :: PRED_NAME -> [SORT] -> [TERM f] -> FORMULA f
genPredication pName sl ts =
    Predication (Qual_pred_name pName 
                                (Pred_type sl []) [])
                ts
                []

genOpEquation :: FunKind -> OP_NAME -> [SORT] -> [TERM f] -> FORMULA f
genOpEquation kind opName sl terms = 
    Strong_equation sortedFunTerm resTerm []
    where sortedFunTerm = 
             Sorted_term (Application 
                            (Qual_op_name opName 
                                          opType [])
                            argTerms
                            []) 
                         resSort       
                         []
          opType = case kind of 
                   Partial -> Op_type Partial argSorts resSort []
                   Total   -> Op_type Total   argSorts resSort []
          argTerms = init terms
          resTerm  = last terms
          argSorts = init sl
          resSort  = last sl


toSortTerm :: TERM f -> TERM f
toSortTerm t@(Qual_var _ s _) = Sorted_term t s []
toSortTerm _ = error "CASL2TopSort.toSortTerm: can only handle Qual_var" 

genVars :: [SORT] -> [TERM f]
genVars = zipWith toVarTerm varSymbs
    where varSymbs = map mkSimpleId 
                         (map (:[]) "xyzuwv"++
                          map (\i -> 'v':show i) [(1::Int)..])
          toVarTerm vs s = (Qual_var vs s [])

genSenName :: Show a => String -> a -> Int -> String
genSenName suff symbName arity =
    "arg_rest_"++ show symbName++'_':suff++'_':show arity

genQuantification :: FORMULA f -- ^ either the predication or 
                               -- function equation
                  -> [TERM f] -- ^ Qual_vars
                  -> (Set.Set [Maybe PRED_NAME]) 
                  -> Maybe (FORMULA f)
genQuantification prop vars spl =
    -- trace (show vds) $
     maybe Nothing  (\dis -> 
        Just (Quantification Universal vds
                             (Implication prop
                                          dis
                                          True []) []))
           (genDisjunction vars spl)
   where vds = reverse (foldl toVarDecl [] vars)
         -- toVarDecl :: [VAR_DECL] -> TERM f -> [VAR_DECL]
         toVarDecl [] (Qual_var n s _) = [Var_decl [n] s []]
         toVarDecl xxs@((Var_decl l s1 []):xs) (Qual_var n s _) 
             | s1 == s   = Var_decl (l++[n]) s1 []:xs
             | otherwise = Var_decl [n] s []:xxs
         toVarDecl _ _ = 
             error "CASL2TopSort.toVarDecl: can only handle Qual_var"
         

genDisjunction :: [TERM f] -- ^ Qual_vars
                  -> (Set.Set [Maybe PRED_NAME])
                  -> Maybe (FORMULA f)
genDisjunction vars spn  
    | Set.size spn == 1 = 
        case genConjunction [] (head (Set.toList spn)) of
        []  -> Nothing
        [x] -> Just x
        _   -> error "CASL2TopSort.genDisjunction: this cannot happen"
    | null disjs        = Nothing
    | otherwise         = Just (Disjunction disjs [])
      where disjs = foldl genConjunction [] (Set.toList spn)
            genConjunction acc pns 
                | null conjs = acc
                | otherwise  = (Conjunction (reverse conjs) []):acc
                where conjs = foldl genPred [] (zip vars pns)
            -- genPred :: TERM f -> PRED_NAME -> FORMULA f
            genPred acc (v@(Qual_var _ s _),mpn) = 
                maybe acc (\pn -> genPredication pn [s] [v]:acc) mpn
            genPred _ _ = 
                error "CASL2TopSort.genPred: can only handle Qual_var"

partitionArity :: Int -> Set.Set PredType -> Map.Map Int [PredType]
partitionArity arity set
    | arity == 1 = Map.insert arity (Set.toList set) Map.empty
    | otherwise = case Set.partition 
		             (\ x -> length (predArgs x) == arity) set of
		  (tt,ff) -> Map.insert arity (Set.toList tt) 
			                (partitionArity (arity-1) ff)

combineTypes :: SubSortMap -> Map.Map Int [PredType] 
	     -> Map.Map Int [Map.Map SORT (Set.Set SORT)]
combineTypes subSortMap = 
    Map.mapWithKey (\ arity types -> 
		       foldr (\ t sl -> zipWith ins (predArgs t) sl) 
                                          (replicate arity Map.empty) types)
    where ins so mp = maybe mp 
		            (\v -> Map.setInsert (topSort_PI v) so mp)
                            (Map.lookup so subSortMap)

-- | Each membership test of a subsort is transformed to a predication
-- of the corresponding unary predicate. Variables quantified over a
-- subsort yield a premise to the quantified formula that the
-- corresponding predicate holds. All typings are adjusted according
-- to the subsortmap and sort generation constraints are translated to
-- disjointness axioms.


transSen :: (Show f) => Sign f e -> FORMULA f -> Result (FORMULA f)
transSen sig f = 
    case (generateSubSortMap (sortSet sig) 
	                     (sortRel sig) 
			     (predMap sig)) of
    Result d Nothing -> Result d Nothing 
    Result d (Just ssm)  -> 
        Result d (Just ( mapSen ssm f ))
                   

mapSen :: (Show f) => SubSortMap -> FORMULA f -> FORMULA f
mapSen subSortMap f = trace (show f) $ 
    case f of
    Conjunction fl pl -> Conjunction (map (mapSen subSortMap) fl) pl
    Disjunction fl pl -> Disjunction (map (mapSen subSortMap) fl) pl
    Implication f1 f2 b pl -> 
        Implication (mapSen subSortMap f1) (mapSen subSortMap f2) b pl
    Equivalence f1 f2 pl -> 
        Equivalence (mapSen subSortMap f1) (mapSen subSortMap f2) pl
    Negation f1 pl -> Negation (mapSen subSortMap f1) pl
    tr@(True_atom _)  -> tr
    fa@(False_atom _) -> fa
    Quantification q vdl f1 pl -> 
        Quantification q (map updateVarDecls vdl) (mapSen subSortMap f1) pl
    Membership t s pl ->
        let t' = mapTerm subSortMap t
        in maybe (Membership t' s pl)
                 (\pn -> genPredication pn [lkupTop subSortMap s]
                                           [t'])
                 (lkupPRED_NAME subSortMap s)
    Existl_equation t1 t2 pl ->
        Existl_equation (mapTerm subSortMap t1) (mapTerm subSortMap t2) pl
    Strong_equation t1 t2 pl ->
        Strong_equation (mapTerm subSortMap t1) (mapTerm subSortMap t2) pl
    Definedness t pl ->
        Definedness (mapTerm subSortMap t) pl
    Predication psy tl pl -> 
        Predication (updatePRED_SYMB psy) (map (mapTerm subSortMap) tl) pl
    Sort_gen_ax cs _ -> genEitherAxiom subSortMap cs
    ExtFORMULA f1 -> ExtFORMULA f1 -- ExtFORMULA stays as it is
    Mixfix_formula _ -> 
        error "CASL2TopSort.mapSen: cannot cope with Mixfix_formula"
    Unparsed_formula _ _ -> 
        error "CASL2TopSort.mapSen: cannot cope with Unparsed_formula"
    where updateVarDecls (Var_decl vl s pl) = 
              Var_decl vl (lkupTop subSortMap s) pl
          updatePRED_SYMB (Pred_name _) = 
              error "CASL2TopSort.mapSen: got untyped predication"
          updatePRED_SYMB (Qual_pred_name pn (Pred_type sl pl') pl) =
              Qual_pred_name pn 
                 (Pred_type (map (lkupTop subSortMap) sl) pl') pl

mapTerm ::(Show f) => SubSortMap -> TERM f -> TERM f
mapTerm ssMap t = 
    case t of
    Simple_id _ -> error "CASL2TopSort.mapTerm: unqualified variable found"
    Qual_var v s pl -> Qual_var v (lTop s) pl
    Application osy tl pl ->
        Application (updateOP_SYMB osy) (map (mapTerm ssMap) tl) pl
    Sorted_term t1 s pl ->
        Sorted_term (mapTerm ssMap t1) (lTop s) pl
    -- casts are discarded due to missing subsorting
    Cast t1 _ _ -> mapTerm ssMap t1
    Conditional t1 f t2 pl ->
        Conditional (mapTerm ssMap t1) (mapSen ssMap f) (mapTerm ssMap t2) pl
    Unparsed_term _ _ -> 
        error "CASL2TopSort.mapTerm: cannot cope with Unparsed_term"
    _ -> 
        error "CASL2TopSort.mapTerm: cannot cope with any Mixfix_*"
    where lTop = lkupTop ssMap
          updateOP_SYMB (Op_name _) =
              error "CASL2TopSort.mapTerm: got untyped application"
          updateOP_SYMB (Qual_op_name on ot pl) =
              Qual_op_name on (updateOP_TYPE ot) pl
          updateOP_TYPE (Op_type fk sl s pl) =  
              Op_type fk (map lTop sl) (lTop s) pl

genEitherAxiom :: SubSortMap -> [Constraint] -> FORMULA f
genEitherAxiom ssMap _ = True_atom [] {- map genImplication
    where genImplication cons =
              Implication prop dis True [] -}
    