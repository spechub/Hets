{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from HasCASL to Isabelle-HOL.

-}

module Comorphisms.HasCASL2IsabelleHOL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Common.Lib.Map as Map
import Common.Lib.Set as Set
import Data.List
import Common.PrettyPrint
import Common.AS_Annotation (Named, mapNamedM)
import Debug.Trace
-- HasCASL
import HasCASL.Logic_HasCASL
-- import HasCASL.Sublogic
-- import HasCASL.MiniAs as MiniAs
-- import HasCASL.MiniLe
import HasCASL.Le
import HasCASL.As as As
import HasCASL.Morphism

-- Isabelle
import Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaPrint

-- | The identity of the comorphism
data HasCASL2IsabelleHOL = HasCASL2IsabelleHOL deriving (Show)

instance Language HasCASL2IsabelleHOL -- default definition is okay

instance Comorphism HasCASL2IsabelleHOL
               HasCASL HasCASL_Sublogics
               BasicSpec As.Term SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = HasCASL
    sourceSublogic _ = () -- HasCASL_SL
--                       { has_sub = False,   -- subsorting
--                         has_part = True,  -- partiality
--                         has_eq = True,    -- equality
--                         has_pred = True,  -- predicates
--                         has_ho = True,  -- higher order
--                         has_type_classes = False,
--                         has_polymorphism = False,
--                         which_logic = FOL
--                       }
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_sign _ = transSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign phi =
      Just $ Sentence {senTerm = (transTerm sign phi)}
    --map_symbol :: cid -> symbol1 -> Set symbol2

------------------------------ Ids ---------------------------------


---------------------------- Signature -----------------------------

-- data Sign = Sign { baseSig :: String, -- like Pure, HOL etc.
--                    tsig :: TypeSig,
--                    constTab :: Map.Map String Typ,
--                    syn :: Syntax
--                  }


transSignature :: Env
                   -> Maybe(IsaSign.Sign,[Named IsaSign.Sentence]) 
transSignature sign = 
  Just(IsaSign.Sign{
    baseSig = "Main",
    tsig = emptyTypeSig 
            {tycons = Map.foldWithKey extractTypeName Map.empty (typeMap sign)},
    constTab = Map.foldWithKey insertOps Map.empty (assumps sign),
    dataTypeTab = [],
    syn = () },
     [] )  -- for now, no sentences
  where 
    extractTypeName typeId _ map = Map.insert (showIsa typeId) 0 map
    insertOps opName opInfs map = 
     let opIs = opInfos opInfs
     in if (length opIs) == 1 then
       Map.insert (showIsa opName) (transOpInfo (head opIs)) map
       else foldl (\m1 (opInf,i) -> Map.insert (showIsaI opName i) (transOpInfo opInf) m1) map
              (zip opIs [1..length opIs])
 
transOpInfo :: OpInfo -> Typ
transOpInfo opInf = case (opDefn opInf) of
                      NoOpDefn Pred -> transPredType (opType opInf)
                      NoOpDefn _    -> transOpType (opType opInf)

transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ (_ :=> opType) _) = transType opType

transPredType :: TypeScheme -> Typ
transPredType  (TypeScheme _ (_ :=> predType) _) = 
       case predType of
         FunType tp _ _ _ -> (transType tp) --> boolType
         _                -> error "Wrong predicate type"
--                                                 (transType predType) --> boolType

transType :: Type -> Typ
transType typ = case typ of
                   TypeName typeId _ _     -> Type(showIsa typeId,[])
                   ProductType types _     -> foldr1 IsaSign.mkProductType (map transType types)
                   FunType type1 _ type2 _ -> (transType type1) --> (mkOptionType (transType type2))

------------------------------ Formulas ------------------------------

transVar :: Var -> String
transVar = showIsa

transTerm :: Env -> As.Term -> IsaSign.Term
transTerm _ (QualVar var typ _) = 
    Const("Some",((transType typ) --> (mkOptionType (transType typ)))) 
      `App`  IsaSign.Free((transVar var,(transType typ)))
transTerm _ (QualOp _ opId _ _) =
       let op = getOp opId
       in
         case op of
           "true"  -> Const ("True",dummyT)
           "false" -> Const ("False",dummyT)
           _       -> Const(op,dummyT)
transTerm sign (ApplTerm term1 term2 _) = 
       case term1 of
         QualOp Fun opId logType _ -> transLog sign term1 term2
-- geht das so mit logType?? Vermutlich nicht!! Falls nicht dann
-- gehen die Ids auch nicht!!!
         _ -> Const("app",dummyT) `App` (transTerm sign term1) 
                                  `App` (transTerm sign term2)
transTerm sign (QuantifiedTerm quant varDecls phi _) = 
  foldr (quantify quant) (transTerm sign phi) (map toPair varDecls)
transTerm sign (TypedTerm term _ typ _) = transTerm sign term
transTerm sign (LambdaTerm pats Partial body _) = 
  Const("Some",dummyT) `App` (foldr (abstraction sign) (transTerm sign body) pats)
transTerm sign (LetTerm Let eqs body _) = 
  transTerm sign (foldr let2lambda body eqs)
transTerm sign (TupleTerm terms _) = foldl1 prod (map (transTerm sign) terms)

let2lambda (ProgEq pat term _) body = 
  ApplTerm (LambdaTerm [pat] Partial body [nullPos]) term [nullPos]


-- data Term =
--         Const (String, Typ)
--       | Free  (String, Typ)
--       | Abs   (String, Typ, Term)
--       | App Term  Term

-- getVarName :: As.Term -> String
-- getVarName term = case term of
--                     QualVar var _ _ -> transVar var
--                     TypedTerm term _ _ _ -> getVarName term
-- --                    TupleTerm terms _ -> evalName terms
--                     _ -> error "Illegal pattern in lambda abstraction"

getType :: As.Term -> Typ
getType term = case term of
                    QualVar _ typ _ -> transType typ
                    TypedTerm _ _ typ _ -> transType typ
--                    TupleTerm terms _ -> evalType terms
                    _ -> error "Illegal pattern in lambda abstraction"

transLog :: Env -> As.Term -> As.Term -> IsaSign.Term
transLog sign (QualOp a opId b c) term = 
       let op = getOp opId
       in
       case op of
         "/\\"  -> (foldl1 binConj (map (transTerm sign) (getPhis term)))
         "\\/"  -> (foldl1 binDisj (map (transTerm sign) (getPhis term)))
         "=>"   -> (binImpl (transTerm sign (head (getPhis term))) 
                           (transTerm sign (last (getPhis term))))
         "<=>"  -> (binEq (transTerm sign (head (getPhis term))) 
                         (transTerm sign (last (getPhis term))))
         "\172" -> (Const ("Not",dummyT) `App` (transTerm sign term))
         "def"  -> (Const ("defOp",dummyT) `App` (transTerm sign term))
--       "=e="   ->
         "="    -> (binEq (transTerm sign (head (getPhis term))) 
                         (transTerm sign (last (getPhis term))))
         _      -> (transTerm sign (QualOp a opId b c)) `App` (transTerm sign term)
       where getPhis (TupleTerm phis _) = phis

getOp (InstOpId uInst _ _) = getTokenName uInst
getTokenName (Id (tok:toks) a b) = if (tokStr tok) == "__" then getTokenName (Id toks a b)
                                     else tokStr tok --trace ("Token...: "++ (show toks) ++ "\n\n") (tokStr (head toks))

-- mkSome :: Var -> String
-- mkSome var = "Some "++(transVar var)

quantify q (v,t) phi  = 
  Const (qname q,dummyT) `App` Abs ((Const(transVar v, dummyT)),transType t,phi)
  where
  qname Universal   = "All"
  qname Existential = "Ex"
  qname Unique      = "Ex1"

binConj phi1 phi2 = 
  Const("op &",dummyT) `App` phi1 `App` phi2
binDisj phi1 phi2 = 
  Const("op |",dummyT) `App` phi1 `App` phi2
binImpl phi1 phi2 = 
  Const("op -->",dummyT) `App` phi1 `App` phi2
binEq phi1 phi2 = 
  Const("op =",dummyT) `App` phi1 `App` phi2

prod term1 term2 =
  Const("Pair",dummyT) `App` term1 `App` term2

abstraction sign pat body = Abs((transTerm sign pat), (getType pat), body)

toPair (GenVarDecl (VarDecl var typ _ _)) = (var,typ)







