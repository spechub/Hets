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
import Data.List
import Common.AS_Annotation (Named)
import Debug.Trace

-- HasCASL
import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
-- import HasCASL.MiniAs as MiniAs
-- import HasCASL.MiniLe
import HasCASL.Le as Le
import HasCASL.As as As
import HasCASL.Builtin
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
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () IsaSign.Sentence () ()
               IsaSign.Sign 
               () () () ()  where
    sourceLogic _ = HasCASL
    sourceSublogic _ = HasCASL_SL
                       { has_sub = False,   -- subsorting
                         has_part = True,  -- partiality
                         has_eq = True,    -- equality
                         has_pred = True,  -- predicates
                         has_ho = True,  -- higher order
                         has_type_classes = False,
                         has_polymorphism = False,
                         has_type_constructors = False,
                         which_logic = FOL
                       }
    targetLogic _ = Isabelle
    targetSublogic _ = ()
    map_sign _ = transSignature
    --map_morphism _ morphism1 -> Maybe morphism2
    map_sentence _ sign phi =
      Just $ Sentence {senTerm = (transSentence sign phi)}
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
    baseSig = "MainHC",
    tsig = emptyTypeSig 
            {tycons = Map.foldWithKey extractTypeName Map.empty (typeMap sign)},
    constTab = Map.foldWithKey insertOps Map.empty (assumps sign),
    dataTypeTab = [],
    syn = () },
    [] )  -- for now, no sentences
   where 
    extractTypeName typeId _ m = Map.insert (showIsa typeId) 0 m
    insertOps opName opInfs m = 
     let opIs = opInfos opInfs
     in if (length opIs) == 1 then
       Map.insert (showIsa opName) (transOpInfo (head opIs)) m
       else foldl (\m1 (opInf,i) -> Map.insert (showIsaI opName i) (transOpInfo opInf) m1) m
              (zip opIs [1..length opIs])
 
transOpInfo :: OpInfo -> Typ
transOpInfo opInf = case (opDefn opInf) of
                      NoOpDefn Pred -> transPredType (opType opInf)
                      NoOpDefn _    -> transOpType (opType opInf)
transOpInfo _ = error "Not supported operation declaration and/or definition"

transOpType :: TypeScheme -> Typ
transOpType (TypeScheme _ (_ :=> op) _) = transType op

transPredType :: TypeScheme -> Typ
transPredType  (TypeScheme _ (_ :=> pre) _) = 
       case pre of
         FunType tp _ _ _ -> (transType tp) --> boolType
         _                -> error "Wrong predicate type"

transType :: Type -> Typ
transType typ = case typ of
                   TypeName typeId _ _     -> Type(showIsa typeId,[])
                   ProductType types _     -> foldr1 IsaSign.mkProductType (map transType types)
                   FunType type1 _ type2 _ -> (transType type1) --> (mkOptionType (transType type2))
transType _ = error "Not supported type in use"

------------------------------ Formulas ------------------------------

transVar :: Var -> String
transVar = showIsa

transSentence :: Env -> Le.Sentence -> IsaSign.Term
transSentence e s = case s of
    Le.Formula t -> transTerm e t
    DatatypeSen _ -> error "transSentence: data type"
    ProgEqSen _ _ _pe -> error "transSentence: program"

transTerm :: Env -> As.Term -> IsaSign.Term
transTerm _ (QualVar var typ _) = 
    let tp = transType typ 
	otp = tp --> mkOptionType tp
	in  Const("Some", otp) `App` IsaSign.Free(transVar var, tp)
transTerm _ (QualOp _ (InstOpId opId _ _) _ _)
  | opId == trueId = Const ("True",dummyT)
  | opId == falseId = Const ("False",dummyT)
  | otherwise = Const("Some",dummyT) `App` Const((getNameOfOpId opId),dummyT)

transTerm sign (ApplTerm term1 term2 _) =
        case term1 of
           QualOp Fun (InstOpId opId _ _) _ _ -> transLog sign opId term1 term2 
           _ ->  Const("app",dummyT) `App` (transTerm sign term1) 
                                     `App` (transTerm sign term2)
transTerm sign (QuantifiedTerm quant varDecls phi _) = 
  foldr (quantify quant) (transTerm sign phi) (map toPair varDecls)
transTerm sign (TypedTerm term _ _ _) = transTerm sign term
transTerm sign (LambdaTerm pats Partial body _) = 
  if (null pats) then   Const("Some",dummyT) `App` Abs(IsaSign.Free("",dummyT),
                                                       dummyT, (transTerm sign body))
    else Const("Some",dummyT) `App` (foldr (abstraction sign) (transTerm sign body) pats)
transTerm sign (LetTerm Let eqs body _) = 
  transTerm sign (foldr let2lambda body eqs)
transTerm sign (TupleTerm terms _) = Const("Some",dummyT) `App` (foldl1 prod (map (transTermAbs sign) terms))
transTerm _ _ = error "Not supported (abstract) syntax in use."

let2lambda :: ProgEq -> As.Term -> As.Term
let2lambda (ProgEq pat term _) body = 
  ApplTerm (LambdaTerm [pat] Partial body [nullPos]) term [nullPos]


-- data Term =
--         Const (String, Typ)
--       | Free  (String, Typ)
--       | Abs   (Term, Typ, Term)
--       | App Term  Term

getType :: As.Term -> Typ
getType term = case term of
                    QualVar _ typ _ ->  transType typ
                    TypedTerm _ _ typ _ -> transType typ
                    TupleTerm terms _ -> evalTupleType terms
                    _ -> error "Illegal pattern in lambda abstraction"
    where evalTupleType t = foldr1 IsaSign.mkProductType (map getType t)

transLog :: Env -> Id -> As.Term -> As.Term -> IsaSign.Term
transLog sign opId term1 term
  | opId == andId = (foldl1 binConj (map (transTerm sign) (getPhis term)))
  | opId == orId = (foldl1 binDisj (map (transTerm sign) (getPhis term)))
  | opId == implId = (binImpl (transTerm sign (head (getPhis term))) 
                           (transTerm sign (last (getPhis term))))
  | opId == eqvId = (binEqv (transTerm sign (head (getPhis term))) 
                         (transTerm sign (last (getPhis term))))
  | opId == notId = (Const ("Not",dummyT) `App` (transTerm sign term))
  | opId == defId = (Const ("defOp",dummyT) `App` (transTerm sign term))
  | opId == exEq = binConj (binConj (binEq (transTerm sign (head (getPhis term))) 
                              (transTerm sign (last (getPhis term))))
                              (Const ("defOp",dummyT) `App` (transTerm sign (head (getPhis term)))))
                           (Const ("defOp",dummyT) `App` (transTerm sign (last (getPhis term))))
  | opId == eqId = (binEq (transTerm sign (head (getPhis term))) 
                         (transTerm sign (last (getPhis term))))
  | otherwise = (transTerm sign term1) `App` (transTerm sign term)
       where getPhis (TupleTerm phis _) = phis

quantify :: Quantifier -> (Var,Type) -> IsaSign.Term -> IsaSign.Term
quantify q (v,t) phi  = 
  Const (qname q,dummyT) `App` Abs ((Const(transVar v, dummyT)),transType t,phi)
  where
  qname Universal   = "All"
  qname Existential = "Ex"
  qname Unique      = "Ex1"

binConj :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binConj phi1 phi2 = 
  Const("op &",dummyT) `App` phi1 `App` phi2

binDisj :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binDisj phi1 phi2 = 
  Const("op |",dummyT) `App` phi1 `App` phi2

binImpl :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binImpl phi1 phi2 = 
  Const("op -->",dummyT) `App` phi1 `App` phi2

binEq :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binEq phi1 phi2 = 
  Const("op =",dummyT) `App` phi1 `App` phi2

-- For precedence disdinction <=>/=
binEqv :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binEqv phi1 phi2 = 
  Const("op <=>",dummyT) `App` phi1 `App` phi2

prod :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
prod term1 term2 =
  Const("Pair",dummyT) `App` term1 `App` term2

abstraction :: Env -> As.Term -> IsaSign.Term -> IsaSign.Term
abstraction sign pat body = Abs((transTermAbs sign pat), getType pat, body)

transTermAbs :: Env -> As.Term -> IsaSign.Term
transTermAbs _ (QualVar var typ _) = IsaSign.Free(transVar var, transType typ)
transTermAbs sign (QualOp a (InstOpId opId b c) d e) = 
  if (isLogId opId) then transTerm sign (QualOp a (InstOpId opId b c) d e)
    else Const((getNameOfOpId opId),dummyT)
transTermAbs sign term = transTerm sign term

getNameOfOpId :: Id -> String
getNameOfOpId (Id [] _ _) = error "Operation without name"
getNameOfOpId (Id (tok:toks) a b) = if (tokStr tok) == "__" then getNameOfOpId (Id toks a b)
                                                else tokStr tok
isLogId :: Id -> Bool
isLogId i = (i == andId) 
         || (i == orId) 
         || (i == implId) 
         || (i == eqvId) 
         || (i == notId) 
         || (i == defId) 
         || (i == exEq) 
         || (i == eqId) 

toPair :: GenVarDecl -> (Var,Type)
toPair (GenVarDecl (VarDecl var typ _ _)) = (var,typ)







