module ToHaskell.TranslateAna where

import HasCASL.As
import HasCASL.Le
import Haskell.Language.Syntax
--import Common.AS_Annotation
import Common.Id
--import Common.Lib.Parsec.Pos
import Common.Lib.Map as Map hiding (map)
import Common.Lexer
import Data.Char
import Data.List
import Common.Token
import Common.AnnoState
import Common.PPUtils

idToHaskell :: AParser WrapString
idToHaskell = fmap (WrapString . translateId) parseId 

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

translateAna :: Env -> HsModule
--translateAna env = error (show env)
translateAna env = HsModule (SrcLoc "" 1 1) (Module "HasCASLModul") Nothing []
                   ((translateTypeMap (typeMap env)) ++ 
                    (translateAssumps (assumps env)))
-- Achtung: env enthält noch andere zu übersetzende Argumente 
-- (z.B. classMap, sentences) !!

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

translateTypeMap :: TypeMap -> [HsDecl]
translateTypeMap m = concat $ map translateData (assocs m)

-- muss translateData eine Liste von HsDecl's oder eine HsDecl liefern?
translateData :: (TypeId, TypeInfo) -> [HsDecl]
translateData (tid,info) = 
  case (typeDefn info) of
    NoTypeDefn ->  -- z.B. bei sorts, was wird daraus?
        ((HsDataDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	            [] -- HsContext
	            (HsIdent (translateIdWithType UpperId tid))
		    [] -- [HsName]
		    [(HsConDecl 
                       (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
                       (HsIdent (translateIdWithType UpperId tid))
		       [])
		    ]
		    [] -- [HsQName]  (für deriving) woher?
	 ):[])
    Supertype _ _ _ -> [] -- ?
    DatatypeDefn _ _ -> 
	((HsDataDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	            [] -- HsContext
	            (HsIdent (translateIdWithType UpperId tid))
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
             [(HsIdent (translateIdWithType LowerId i))]
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
  MixfixType _ -> error ("unexpected type (MixfixType): " ++ show t)
  KindedType kt _kind _poslist -> translateType kt
  BracketType _ _ _ -> error ("unexpected type (BracketType): " ++ show t)
  TypeToken _ -> error ("unexpected type (TypeToken): " ++ show t)
  TypeAppl t1 t2 -> HsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> 
      if n > 0 then
	 HsTyVar (HsIdent (translateIdWithType LowerId tid))
      else
         HsTyCon (UnQual (HsIdent (translateIdWithType UpperId tid)))
--Missing: Übersetzung der Kind's             

{------------------------------------------------------------------------
 Translation of Id's
 HasCASL  ->      Haskell
  :                ::       (Typangabe)
  ::               :        (Listenkonkatenation)
  Opname           a___Opname
  conname          A___conname
  Reserviert       _r_<Ersatzzeichen>
  Symbole          _Z_<Symbolzersatzzeichen>

Ersatzzeichen für reservierte Zeichen und für Symbole:
-- Special / reserviert
    _  -> _1
    __ -> _2
    {  -> _b
    }  -> _d
    [  -> _s
    ]  -> _q
    .  -> _p

-- Symbole
    +  -> _P
    -  -> _M
    *  -> _T
    /  -> _D
    \  -> _B
    &  -> _A
    =  -> _E
    <  -> _L
    >  -> _G
    !  -> _I
    ?  -> _Q
    :  -> _C
    $  -> _S
    @  -> _O
    #  -> _H
    ^  -> _V
    ~  -> _N
------------------------------------------------------------------------}

translateIdWithType :: IdCase -> Id -> String
translateIdWithType ty (Id tlist _idlist _poslist) = 
  let s = translateId (Id tlist _idlist _poslist)
  in if ty == UpperId then
        if isLower $ head $ tokStr $ head tlist then
	  "A_" ++ s
	else firstDigit s
     else -- if ty == LowerId then
        if isUpper $ head $ tokStr $ head tlist then
           "a_" ++ s
        else firstDigit s


data IdCase = UpperId | LowerId deriving (Eq,Show)


translateId :: Id -> String
translateId (Id tlist idlist _poslist) = 
    (translateTokens tlist) ++ (translateCompound idlist)


translateTokens :: [Token] -> String
translateTokens [] = ""
translateTokens (t:ts) = 
    let str = tokStr t
        res = translateTokens ts in
    if isPlace t then
      subPlace ++ res
    else (concatMap symbolMapping str) ++ res

startsWithDigit :: String -> Bool
startsWithDigit s = isDigit $ head s

firstDigit :: String -> String
firstDigit s = if startsWithDigit s then
	         "_D" ++ s
	       else s

subPlace :: String
subPlace = "_2"

symbolMapping :: Char -> String
symbolMapping c = case c of 
-- Special / reserviert
    '_'  -> "_1"    -- \95
    '{'  -> "_b"    -- \123
    '}'  -> "_r"    -- \125
    '['  -> "_s"    -- \91
    ']'  -> "_q"    -- \93
    '.'  -> "_d"    -- \46
    '\'' -> "_p"
-- Symbole
    '+'  -> "_P"    -- \43
    '-'  -> "_M"    -- \45
    '*'  -> "_T"    -- \42
    '/'  -> "_D"    -- \47
    '\\' -> "_B"    -- \92
    '&'  -> "_A"    -- \38
    --'='  ->       -- \61
    '<'  -> "_L"    -- \60
    '>'  -> "_G"    -- \62
    '!'  -> "_E"    -- \33
    '?'  -> "_Q"    -- \63
    ':'  -> "_C"    -- \58
    '$'  -> "_S"    -- \36
    '@'  -> "_O"    -- \64
    '#'  -> "_H"    -- \35
    '^'  -> "_V"    -- \94
    '|'  -> "_I"    -- \124
    '~'  -> "_N"    -- \126
    '¡'  -> "_e"    -- \161
    '¢'  -> "_c"    -- \162   
    '£'  -> "_l"    -- \163
    '§'  -> "_f"    -- \167
    '©'  -> "_a"    -- \169
    '¬'  -> "_n"    -- \172
    '°'  -> "_h"    -- \176
    '±'  -> "_k"    -- \177
    '²'  -> "_w"    -- \178
    '³'  -> "_t"    -- \179
    'µ'  -> "_y"    -- \181
    '¶'  -> "_j"    -- \182
    '·'  -> "_i"    -- \183
    '¹'  -> "_o"    -- \185
    '¿'  -> "_q"    -- \191
    '×'  -> "_m"    -- \215
    '÷'  -> "_g"    -- \247
    _    -> [c]


translateCompound :: [Id] -> String
--  [      ,      ]
-- _C     _k     _J
translateCompound [] = ""
translateCompound ids = "_C" ++
                        (concat $ intersperse "_k" $ map translateId ids) ++
                        "_J"

