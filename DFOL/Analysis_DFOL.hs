{- |
Module      :  $Header$
Description :  Static analysis for first-order logic with dependent types (DFOL)
-}

module DFOL.Analysis_DFOL
  (
    basicAnalysis         -- static analysis of basic specifications
  , symbAnalysis          -- static analysis for symbols lists
  , symbMapAnalysis       -- static analysis for symbol map lists   
  ) where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Symbol
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Data.Maybe
import qualified Common.Result as Result
import qualified Common.AS_Annotation as Anno
import qualified Data.Set as Set
import qualified Data.Map as Map

-- datatype for items annotated with diagnostic messages 
data DIAGN a = Diagn
    { diags :: [Result.Diagnosis]
    , item  :: a
    } deriving (Show, Eq) 

-- conjunction for a list of truth values with diagnostic messages 
andD :: [DIAGN Bool] -> DIAGN Bool
andD xs = Diagn diag result
          where result = and $ map item xs
                diag = concat $ map diags xs   

-- BASIC SPEC ANALYSIS
basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos) -> Result.Result (BASIC_SPEC, ExtSign Sign Symbol, [Anno.Named FORMULA])
basicAnalysis (bs, sig, _) = if errs then Result.Result diag Nothing else Result.Result [] $ Just (bs, ExtSign newSig declaredSyms, formulae)
                             where Diagn diag1 newSig   = makeSig bs sig
                                   Diagn diag2 formulae = makeFormulas bs newSig                        
                                   declaredSyms         = Set.map Symbol $ Set.difference (getSymbols newSig) (getSymbols sig)
                                   diag                 = diag1 ++ diag2                                     
 	                           errs                 = Result.hasErrors diag

-- SIGNATURES                                                                            
-- make a new signature out of a basic spec and an input signature
makeSig :: BASIC_SPEC -> Sign -> DIAGN Sign
makeSig (Basic_spec items) sig = addItemsToSig items sig 

-- adds a list of annotated basic items to an input signature
addItemsToSig :: [Anno.Annoted BASIC_ITEM] -> Sign -> DIAGN Sign
addItemsToSig [] sig = Diagn [] sig
addItemsToSig (i:is) sig = case i of
                                (Anno.Annoted (Axiom_item _) _ _ _) -> addItemsToSig is sig
                                (Anno.Annoted (Decl_item d) _ _ _) -> if (Result.hasErrors diag)
                                                                         then Diagn diag sig   
                                                                         else addItemsToSig is newSig 
                                                                      where Diagn diag newSig = addDeclToSig d sig             

-- adds a declaration to an existing signature
addDeclToSig :: DECL -> Sign -> DIAGN Sign
addDeclToSig dec sig = if valid then Diagn [] $ addSymbolDecl dec sig else Diagn diag sig    
                       where Diagn diag valid = isValidDecl dec sig emptyContext                                

-- determines whether a declaration is valid w.r.t. a signature and a context 
isValidDecl :: DECL -> Sign -> CONTEXT -> DIAGN Bool
isValidDecl ([],_) _ _ = Diagn [] False  -- ADD DIAGN
isValidDecl (ns,t) sig cont = andD [validNames, validType]
                              where validNames = areValidNames ns sig cont
                                    validType  = isValidType t sig cont 

-- determines whether a variable declaration is valid w.r.t. a signature and a context 
isValidVarDecl :: DECL -> Sign -> CONTEXT -> DIAGN Bool
isValidVarDecl d@(_,t) sig cont = case t of
                                       Univ _ -> isValidDecl d sig cont
                                       _ -> Diagn [wrongDeclTypeError d cont] False
                               
-- determines whether a list of names in a declaration is valid w.r.t. a signature and a context 
areValidNames :: [NAME] -> Sign -> CONTEXT -> DIAGN Bool
areValidNames names sig cont = if (Set.null overlap) 
                                  then Diagn [] True 
                                  else Diagn [redeclaredNamesError overlap cont] False 
                               where declaredSyms = Set.union (getSymbols sig) (getVars cont)
                                     newSyms      = Set.fromList names
                                     overlap      = Set.intersection newSyms declaredSyms
                                                                                  
-- determines whether a type is valid w.r.t. a signature and a context 
isValidType :: TYPE -> Sign -> CONTEXT -> DIAGN Bool
isValidType Sort _ _ = Diagn [] True
isValidType Form _ _ = Diagn [] True
isValidType (Univ t) sig cont = hasType t Sort sig cont
isValidType (Func ts) sig cont = if (length ts < 2)
                                    then Diagn [] False    -- ADD DIAGN
                                    else andD $ map (\t -> isValidType t sig cont) ts
isValidType (Pi [] _) _ _ = Diagn [] False -- ADD DIAGN
isValidType (Pi [d] t) sig cont = andD [validDecl, validType]  
                                  where validDecl = isValidVarDecl d sig cont
                                        validType = isValidType t sig (addVarDecl d cont)
isValidType (Pi (d:ds) t) sig cont = andD [validDecl, validType]                              
                                     where validDecl = isValidVarDecl d sig cont
                                           validType = isValidType (Pi ds t) sig (addVarDecl d cont)

-- determines whether a term has the given type w.r.t. a signature and a context 
hasType :: TERM -> TYPE -> Sign -> CONTEXT -> DIAGN Bool
hasType term expectedType sig cont = case inferredTypeM of
                                          Just inferredType -> if (inferredType == expectedType) 
                                                                  then Diagn [] True 
                                                                  else Diagn [wrongTypeError expectedType inferredType term cont] False
                                          Nothing -> Diagn diag False  
                                     where Result.Result diag inferredTypeM = getType term sig cont                                           
         
-- determines the type of a term w.r.t. a signature and a context 
getType ::TERM -> Sign -> CONTEXT -> Result.Result TYPE
getType (Identifier n) sig cont = case fromSig of
                                       Just type1 -> Result.Result [] $ Just $ alphaRename type1 sig cont
                                       Nothing -> case fromContext of
                                                       Just type1 -> Result.Result [] $ Just $ alphaRename type1 sig cont
                                                       Nothing -> Result.Result [unknownIdentifierError n cont] Nothing         
                                  where fromSig = getSymbolType n sig 
                                        fromContext = getVarType n cont 
getType (Appl f [a]) sig cont = 
    case typeAM of
         Nothing -> Result.Result diagA Nothing 
         Just typeA -> case typeFM of
                            Nothing -> Result.Result diagF Nothing 
                            Just (Func [dom,cod]) -> if (dom == typeA) 
                                                        then Result.Result [] $ Just cod 
                                                        else Result.Result [wrongTypeError dom typeA a cont] Nothing  
                            Just (Func (t:ts)) -> if (t == typeA) 
                                                     then Result.Result [] $ Just $ Func ts 
                                                     else Result.Result [wrongTypeError t typeA a cont] Nothing
                            Just (Pi [([x],t)] typ) -> if (t == typeA) 
                                                          then Result.Result [] $ Just $ substituteTermInType x a typ 
                                                          else Result.Result [wrongTypeError t typeA a cont] Nothing
                            Just (Pi (([x],t):ds) typ) -> if (t == typeA) 
                                                             then Result.Result [] $ Just $ substituteTermInType x a $ Pi ds typ 
                                                             else Result.Result [wrongTypeError t typeA a cont] Nothing
                            Just (Pi (((x:xs),t):ds) typ) -> if (t == typeA) 
                                                                then Result.Result [] $ Just $ substituteTermInType x a $ Pi ((xs,t):ds) typ 
                                                                else Result.Result [wrongTypeError t typeA a cont] Nothing
                            Just typeF -> Result.Result [noFunctionTypeError f typeF cont] Nothing
    where Result.Result diagF typeFM = getType f sig cont
          Result.Result diagA typeAM = getType a sig cont
getType term sig cont = getType (termApplForm term) sig cont

-- renames variables in a Pi type to avoid variable capture
alphaRename :: TYPE -> Sign -> CONTEXT -> TYPE
alphaRename t sig cont = case t of
                              Pi _ _ -> foldl (\ t1 (v1,v2) -> substituteVarInType v1 v2 t1) t varsRenames
                              _ -> t
                         where vars  = Set.toList $ getVarsInType t
                               varsRenames = renameVars vars $ Set.union (getSymbols sig) (getVars cont)

-- renames all variables in the given list to avoid overlap with the given set of names 
renameVars :: [NAME] -> Set.Set NAME -> [(NAME,NAME)]
renameVars [] _ = []
renameVars (var:vars) names = if (Set.notMember var names)
                                 then let renamedVars = renameVars vars $ Set.insert var names
                                          in (var,var):renamedVars
                                 else let newVar = Token ((tokStr var) ++ "1") nullRange
                                          ((_,renamedVar):renamedVars) = renameVars (newVar:vars) names
                                          in (var,renamedVar):renamedVars                                                          

-- FORMULAS                                                                  
-- make a list of formulas for the given signature out of a basic spec
makeFormulas :: BASIC_SPEC -> Sign -> DIAGN [Anno.Named FORMULA]
makeFormulas (Basic_spec items) sig = makeFormulasFromItems items 0 sig

-- make a list of named formulas out of a list of annotated items 
makeFormulasFromItems :: [Anno.Annoted BASIC_ITEM] -> Int -> Sign -> DIAGN [Anno.Named FORMULA]
makeFormulasFromItems [] _ _ = Diagn [] []
makeFormulasFromItems (i:is) num sig = 
    case i of
         (Anno.Annoted (Decl_item _) _ _ _) -> makeFormulasFromItems is num sig
         (Anno.Annoted (Axiom_item a) _ _ annos) -> case fM of
                                                         Just f -> Diagn diagL (f:fs)
                                                                   where Diagn diagL fs = makeFormulasFromItems is newNum sig 
                                                         Nothing -> Diagn (diag ++ diagL) fs 
                                                                    where Diagn diagL fs = makeFormulasFromItems is num sig
                                                    where Result.Result diag fM = makeNamedFormula a nam annos sig 
                                                          label                 = Anno.getRLabel i
                                                          nam                   = if (label == "") then "Ax_" ++ show num else label
                                                          newNum                = if (label == "") then num + 1 else num                      

-- make a named formula                                   
makeNamedFormula :: FORMULA -> String -> [Anno.Annotation] -> Sign -> Result.Result (Anno.Named FORMULA)
makeNamedFormula f nam annos sig = if valid then Result.Result [] $ Just $ namedF else Result.Result diag Nothing 
                                   where Diagn diag valid = isValidFormula f sig emptyContext
                                         namedF           = (Anno.makeNamed nam f) {Anno.isAxiom = not isTheorem} 
                                         isImplies        = or $ map Anno.isImplies annos
                                         isImplied        = or $ map Anno.isImplied annos 
                                         isTheorem        = isImplies || isImplied   

-- determines whether a formula is valid w.r.t. a signature and a context 
isValidFormula :: FORMULA -> Sign -> CONTEXT -> DIAGN Bool
isValidFormula T _ _ = Diagn [] True
isValidFormula F _ _ = Diagn [] True 
isValidFormula (Pred t) sig cont = hasType t Form sig cont
isValidFormula (Equality term1 term2) sig cont = case type1M of
                                                      Nothing -> Diagn diag1 False
                                                      Just type1 -> case type1 of
                                                                         Univ _ -> hasType term2 type1 sig cont
                                                                         _ -> Diagn [noUnivTypeError term1 type1 cont] False
                                                 where Result.Result diag1 type1M = getType term1 sig cont                                             
isValidFormula (Negation f) sig cont = isValidFormula f sig cont
isValidFormula (Conjunction fs) sig cont = andD $ map (\f -> isValidFormula f sig cont) fs  
isValidFormula (Disjunction fs) sig cont = andD $ map (\f -> isValidFormula f sig cont) fs
isValidFormula (Implication f g) sig cont = andD [isValidFormula f sig cont, isValidFormula g sig cont]                                               
isValidFormula (Equivalence f g) sig cont = andD [isValidFormula f sig cont, isValidFormula g sig cont]
isValidFormula (Forall [] f) sig cont = isValidFormula f sig cont
isValidFormula (Forall (d:ds) f) sig cont = andD [validDecl, validFormula]  
                                            where validDecl    = isValidVarDecl d sig cont
                                                  validFormula = isValidFormula (Forall ds f) sig (addVarDecl d cont)
isValidFormula (Exists [] f) sig cont = isValidFormula f sig cont
isValidFormula (Exists (d:ds) f) sig cont = andD [validDecl, validFormula]  
                                            where validDecl    = isValidVarDecl d sig cont
                                                  validFormula = isValidFormula (Exists ds f) sig (addVarDecl d cont)

-- SYMBOL LIST AND MAP ANALYSIS
-- creates a symbol map out of a list of symbol map items 
symbMapAnalysis :: [SYMB_MAP_ITEMS] -> Result.Result (Map.Map Symbol Symbol)
symbMapAnalysis xs = Result.Result [] $ Just $ foldl (\ m x -> Map.union m (makeSymbMap x)) Map.empty xs

-- creates a symbol map out of symbol map items
makeSymbMap :: SYMB_MAP_ITEMS -> Map.Map Symbol Symbol
makeSymbMap (Symb_map_items xs) = foldl (\ m x -> case x of
                                                       Symb s -> Map.insert (Symbol s) (Symbol s) m
                                                       Symb_map s1 s2 -> Map.insert (Symbol s1) (Symbol s2) m
                                        )
                                        Map.empty 
                                        xs

-- creates a symbol list out of a list of symbol items
symbAnalysis :: [SYMB_ITEMS] -> Result.Result [Symbol]
symbAnalysis xs = Result.Result [] $ Just $ concat $ map makeSymbols xs

-- creates a symbol list out of symbol item
makeSymbols :: SYMB_ITEMS -> [Symbol]
makeSymbols (Symb_items symbs) = map Symbol symbs 

-- ERROR MESSAGES
unknownIdentifierError :: NAME -> CONTEXT -> Result.Diagnosis
unknownIdentifierError n cont = Result.Diag 
                                  { Result.diagKind = Result.Error 
                                  , Result.diagString = "Unknown identifier " ++ (show $ pretty n) ++ " in the context " ++ (show $ pretty cont) 
                                  , Result.diagPos = nullRange
                                  }
wrongTypeError :: TYPE -> TYPE -> TERM -> CONTEXT -> Result.Diagnosis 
wrongTypeError type1 type2 term cont = Result.Diag 
                                         { Result.diagKind = Result.Error 
                                         , Result.diagString = "Term " ++ (show $ pretty term) ++ " must be of type " ++ (show $ pretty type1) ++ 
                                                               " but is of type " ++ (show $ pretty type2) ++ " in context " ++ (show $ pretty cont) 
                                         , Result.diagPos = nullRange
                                         } 

noFunctionTypeError :: TERM -> TYPE -> CONTEXT -> Result.Diagnosis
noFunctionTypeError term t cont = Result.Diag
                                    { Result.diagKind = Result.Error
                                    , Result.diagString = "Term " ++ (show $ pretty term) ++ " has the non-function type " ++ (show $ pretty t) ++  
                                                          " in the context " ++ (show $ pretty cont) ++ " and hence cannot be applied to an argument."
                                    , Result.diagPos = nullRange
                                    } 

noUnivTypeError :: TERM -> TYPE -> CONTEXT -> Result.Diagnosis
noUnivTypeError term t cont = Result.Diag 
                                 { Result.diagKind = Result.Error 
                                 , Result.diagString = "Term " ++ (show $ pretty term) ++ " has the non-discourse type " ++ (show $ pretty t) ++  
                                                       " in the context " ++ (show $ pretty cont) ++ " and hence cannot be used in an equality."
                                 , Result.diagPos = nullRange
                                 }

wrongDeclTypeError :: DECL -> CONTEXT -> Result.Diagnosis 
wrongDeclTypeError d@(_,t) cont = Result.Diag 
                                    { Result.diagKind = Result.Error 
                                    , Result.diagString = "The declaration " ++ (show $ pretty d) ++ " has a non-discourse type " ++ (show $ pretty t) ++ 
                                                          " in context " ++ (show $ pretty cont) 
                                    , Result.diagPos = nullRange
                                    }

redeclaredNamesError :: Set.Set NAME -> CONTEXT -> Result.Diagnosis
redeclaredNamesError ns cont = Result.Diag
                                 { Result.diagKind = Result.Error 
                                 , Result.diagString = "Symbols or variables " ++ show ns ++ " declared previously in the context " 
                                                       ++ (show $ pretty cont) ++ " or in the signature."
                                 , Result.diagPos = nullRange
                                 }
