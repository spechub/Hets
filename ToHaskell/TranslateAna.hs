module ToHaskell.TranslateAna where

import HasCASL.As
import HasCASL.Le
import Haskell.Language.Syntax
--import Common.AS_Annotation
import Common.Id
--import Common.Lib.Parsec.Pos
import Common.Lib.Map as Map hiding (map)
--import Char

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

translateAna :: Env -> HsModule
translateAna env = error (show env)
translateAna env = HsModule (SrcLoc "" 1 1) (Module "HasCASLModul") Nothing []
                   ((translateTypeMap (typeMap env)) ++ 
                    (translateAssumps (assumps env)))
-- Achtung: env enthält noch andere zu übersetzende Argumente 
-- (z.B. ClassMap) !!

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

translateTypeMap :: TypeMap -> [HsDecl]
translateTypeMap m = concat $ map translateType (assocs m)

-- muss translateType eine Liste von HsDecl's oder eine HsDecl liefern?
translateType :: (TypeId, TypeInfo) -> [HsDecl]
translateType (tid,info) = 
  case (typeDefn info) of
    NoTypeDefn -> [] -- z.B. bei sorts, was wird daraus?
    Supertype _ _ _ -> [] -- ?
    DatatypeDefn _ -> 
	((HsDataDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	            [] -- HsContext
	            (HsIdent (translateId Type tid))
		    [] -- [HsName]
		    [] -- [HsConDecl] woher?? (im Env nicht enthalten?)
		    [] -- [HsQName]  (für deriving) woher?
	 ):[])
    AliasTypeDefn _ -> [] -- ?
    TypeVarDefn -> [] -- ?


-------------------------------------------------------------------------
-- Translation of functions
-------------------------------------------------------------------------

translateAssumps :: Assumps -> [HsDecl]
translateAssumps m = concat $ map translateAssump (assocs m)

translateAssump :: (Id,[OpInfo]) -> [HsDecl]
translateAssump _ = []

-------------------------------------------------------------------------
-- Translation of Id's
-------------------------------------------------------------------------

translateId :: IdType -> Id -> String
translateId _ _ = ""

data IdType = Type
	    | Fun