module Comorphisms.HC2I_Utils where

import Common.Id
import qualified Common.Lib.Map as Map
import Data.List

import HasCASL.As
import HasCASL.Le as Le

import Isabelle.IsaSign as IsaSign
import Isabelle.IsaPrint


getNameOfOpId :: Id -> String
getNameOfOpId (Id [] _ _) = error "[Comorphims.HasCASL2IsabelleHOL] Operation without name"
getNameOfOpId (Id (tok:toks) a b) = 
  if (tokStr tok) == "__" then getNameOfOpId (Id toks a b)
    else tokStr tok

transOpId :: Env -> UninstOpId -> TypeScheme -> String
transOpId sign op ts = 
  case (do ops <- Map.lookup op (assumps sign)
           if isSingle (opInfos ops) then return $ showIsa op
             else do i <- elemIndex ts (map opType (opInfos ops))
                     return $ showIsaI op (i+1)) of
    Just str -> str  
    Nothing  -> showIsa op


toPair :: GenVarDecl -> (Var,Type)
toPair (GenVarDecl (VarDecl var typ _ _)) = (var,typ)
toPair _ = error "[Comorphisms.HasCASL2IsabelleHOL] Not supported GenVarDecl"


binConst :: String -> IsaSign.Term -> IsaSign.Term -> IsaSign.Term
binConst s t1 t2 = termAppl (termAppl (con s) t1) t2


termAppl :: IsaSign.Term -> IsaSign.Term -> IsaSign.Term
termAppl t1 t2 = t1 `App` t2


con :: String -> IsaSign.Term
con s = Const(s, noType)

conSome :: IsaSign.Term
conSome = con "Some"

conSomeT :: Typ -> IsaSign.Term
conSomeT t = Const("Some", t)

defOp :: IsaSign.Term
defOp = con "defOp"


conj :: String
conj = "op &"

disj :: String
disj = "op |"

impl :: String
impl = "op -->"

eqv :: String
eqv = "op <=>"

eq :: String
eq = "op ="

pairC :: String
pairC = "pair"

isaPair :: String
isaPair = "Pair"

some :: String
some = "Some"
