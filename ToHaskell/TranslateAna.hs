module ToHaskell.TranslateAna where

import HasCASL.As
import HasCASL.Le
import Haskell.Language.Syntax
--import Common.AS_Annotation
import Common.Id
--import Common.Lib.Parsec.Pos
import Common.Lib.Map as Map hiding (map)
import Char

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

translateAna :: Env -> HsModule
--translateAna env = error (show env)
translateAna env = HsModule (SrcLoc "" 1 1) (Module "HasCASLModul") Nothing []
                   ((translateTypeMap (typeMap env)) ++ 
                    (translateAssumps (assumps env)))
-- Achtung: env enthält noch andere zu übersetzende Argumente 
-- (z.B. ClassMap) !!

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

translateTypeMap :: TypeMap -> [HsDecl]
translateTypeMap m = concat $ map translateData (assocs m)

-- muss translateData eine Liste von HsDecl's oder eine HsDecl liefern?
translateData :: (TypeId, TypeInfo) -> [HsDecl]
translateData (tid,info) = 
  case (typeDefn info) of
    NoTypeDefn -> [] -- z.B. bei sorts, was wird daraus?
    Supertype _ _ _ -> [] -- ?
    DatatypeDefn _ -> 
	((HsDataDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	            [] -- HsContext
	            (HsIdent (translateId TypeId tid))
		    [] -- [HsName]
		    [] -- [HsConDecl] woher?? (im Env nicht enthalten?)
		    [] -- [HsQName]  (für deriving) woher?
	 ):[])
    AliasTypeDefn _ -> [] -- ?
    TypeVarDefn -> [] -- ?
-- Achtung: falsche Positionsangabe

-------------------------------------------------------------------------
-- Translation of functions
-------------------------------------------------------------------------

translateAssumps :: Assumps -> [HsDecl]
translateAssumps m = concat $ map translateAssump (assocs m)

translateAssump :: (Id,[OpInfo]) -> [HsDecl]
translateAssump (_, []) = []
translateAssump (i, (x:xs)) = ((translateSignature i x):
                               (translateAssump (i, xs)))

translateSignature :: Id -> OpInfo -> HsDecl
translateSignature i opinf = 
  HsTypeSig (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
             [(HsIdent (translateId FunId i))]
             (HsQualType [] (translateTypeScheme (opType opinf)))
-- Achtung: falsche Positionsangabe

translateTypeScheme :: TypeScheme -> HsType
translateTypeScheme (TypeScheme _arglist (_plist :=> t) _poslist) = 
  (translateType t)

translateType :: Type -> HsType
translateType t = case t of
  FunType t1 _arr t2 _poslist -> HsTyFun (translateType t1) (translateType t2)
  ProductType tlist _poslist -> HsTyTuple (map translateType tlist)
  LazyType lt _poslist -> translateType lt
  MixfixType _ -> error ("unexpected type: " ++ show t)
  KindedType kt _kind _poslist -> translateType kt
  BracketType _ _ _ -> error ("unexpected type: " ++ show t)
  TypeToken _ -> error ("unexpected type: " ++ show t)
  TypeAppl t1 t2 -> HsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> if n > 0 then
			    HsTyVar (HsIdent (translateId VarId tid))
			  else
			    HsTyCon (UnQual (HsIdent (translateId ConId tid)))
             

{------------------------------------------------------------------------
 Translation of Id's
 HasCASL  ->      Haskell
  :                ::       (Typangabe)
  ::               :        (Listenkonkatenation)
  Opname           a___Opname
  conname          C___conname
  symbolzeichen    S___symbolbuchstabe
  #                S___h
  +                S___p
  -                S___m
  *                S___t
  /                S___d
.......
  compoundlist
------------------------------------------------------------------------}

translateId :: IdType -> Id -> String
translateId t (Id tlist _idlist _poslist) = case t of
  TypeId -> if length tlist == 1 then
              if isLower $ head $ tokStr $ head tlist then
	        ("C___" ++ (tokStr $ head tlist))
              else (tokStr $ head tlist)
            else "" -- length tlist > 1, also mixfix identifier
  ConId -> if length tlist == 1 then
              if isLower $ head $ tokStr $ head tlist then
	        ("C___" ++ (tokStr $ head tlist))
              else (tokStr $ head tlist)
            else "" -- length tlist > 1, also mixfix identifier
  FunId  -> if length tlist == 1 then
              if isUpper $ head $ tokStr $ head tlist then
	        ("a___" ++ (tokStr $ head tlist))
              else (tokStr $ head tlist)
            else "" -- length tlist > 1, also mixfix identifier 
  VarId  -> if length tlist == 1 then
              if isUpper $ head $ tokStr $ head tlist then
	        ("a___" ++ (tokStr $ head tlist))
              else (tokStr $ head tlist)
            else "" -- length tlist > 1, also mixfix identifier 


data IdType = TypeId
	     | FunId
	     | VarId
	     | ConId