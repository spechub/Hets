module ToHaskell.TranslateAna where

import HasCASL.As
import HasCASL.Le
import Haskell.Language.Syntax
--import Common.AS_Annotation
import Common.Id
--import Common.Lib.Parsec.Pos
import Common.Lib.Map as Map hiding (map)
import Common.Lexer
import Char
import List

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
	            (HsIdent (translateIdWithType TypeId tid))
		    [] -- [HsName]
		    [(HsConDecl 
                       (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
                       (HsIdent (translateIdWithType ConId tid))
		       [])
		    ]
		    [] -- [HsQName]  (für deriving) woher?
	 ):[])
    Supertype _ _ _ -> [] -- ?
    DatatypeDefn _ _ -> 
	((HsDataDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	            [] -- HsContext
	            (HsIdent (translateIdWithType TypeId tid))
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
             [(HsIdent (translateIdWithType FunId i))]
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
  TypeName tid _kind n -> if n > 0 then
			    HsTyVar (HsIdent (translateIdWithType VarId tid))
			  else
			    HsTyCon (UnQual (HsIdent (translateIdWithType ConId tid)))
             

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

translateIdWithType :: IdType -> Id -> String
translateIdWithType ty (Id tlist _idlist _poslist) = 
  let s = translateId (Id tlist _idlist _poslist)
  in if (ty == TypeId || ty == ConId) then
        if isLower $ head $ tokStr $ head tlist then
	  "A_" ++ s
	else s
     else -- if (ty == FunId || ty == VarId) then
        if isUpper $ head $ tokStr $ head tlist then
           "a_" ++ s
        else s


data IdType = TypeId
	     | FunId
	     | VarId
	     | ConId
	    deriving (Eq,Show)

translateId :: Id -> String
translateId (Id tlist idlist _poslist) = 
    (translateTokens tlist) ++ (translateCompound idlist)

translateTokens :: [Token] -> String
translateTokens [] = ""
translateTokens (t:ts) = 
    let str = tokStr t
        res = translateTokens ts in
    if isMultiSign str then
      (multiSignMapping str) ++ res
    else (concatMap symbolMapping str) ++ res

--isSign :: Char -> Bool
--isSign c = any (c ==) signChars

isMultiSign :: String -> Bool
isMultiSign s = any (s ==) multiSigns

multiSigns :: [String]
multiSigns = ["__","||","==","&&","/\\","\\/","::"]
-- to be completed

multiSignMapping :: String -> String
multiSignMapping _ = ""

symbolMapping :: Char -> String
symbolMapping c = case c of 
-- Special / reserviert
    '_' -> "_1"     -- \95
    '{' -> "_b"     -- \123
    '}' -> "_r"     -- \125
    '['  -> "_s"    -- \91
    ']'  -> "_q"    -- \93
    '.'  -> "_d"    -- \46

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
    '§'  -> "_p"    -- \167
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


{-translateTokens :: LSS -> [Token] -> String
translateTokens _ [] = ""
translateTokens lss tlist = 
  let t = tokStr (head tlist)
      specialRes = translateTokens TrSpecial (tail tlist) 
      symbolRes = translateTokens TrSymbol (tail tlist) in
  case t of
   
-- Special 
    "_"  -> if lss == TrSpecial then "_1" ++ specialRes
	    else "_r_1" ++ specialRes
    "__" -> if lss == TrSpecial then "_2" ++ specialRes
	    else "_r_2" ++ specialRes
    "{"  -> if lss == TrSpecial then "_b" ++ specialRes
	    else "_r_b" ++ specialRes
    "}"  -> if lss == TrSpecial then "_d" ++ specialRes
	    else "_r_d" ++ specialRes
    "["  -> if lss == TrSpecial then "_s" ++ specialRes
	    else "_r_s" ++ specialRes
    "]"  -> if lss == TrSpecial then "_q" ++ specialRes
	    else "_r_q" ++ specialRes
    "."  -> if lss == TrSpecial then  "_p" ++ specialRes
	    else "_r_p" ++ specialRes

-- Symbols 
    "+"  -> if lss == TrSymbol then "_P" ++ symbolRes
	    else "_Z_P" ++ symbolRes
    "-"  -> if lss == TrSymbol then "_M" ++ symbolRes
	    else "_Z_M" ++ symbolRes
    "*"  -> if lss == TrSymbol then "_T" ++ symbolRes
	    else "_Z_T" ++ symbolRes
    "/"  -> if lss == TrSymbol then "_D" ++ symbolRes
	    else "_Z_D" ++ symbolRes
    "\\" -> if lss == TrSymbol then "_B" ++ symbolRes
	    else "_Z_B" ++ symbolRes     -- \
    "&"  -> if lss == TrSymbol then "_A" ++ symbolRes
	    else "_Z_A" ++ symbolRes
    "="  -> if lss == TrSymbol then "_E" ++ symbolRes
	    else "_Z_E" ++ symbolRes
    "<"  -> if lss == TrSymbol then "_L" ++ symbolRes
	    else "_Z_L" ++ symbolRes
    ">"  -> if lss == TrSymbol then "_G" ++ symbolRes
	    else "_Z_G" ++ symbolRes
    "!"  -> if lss == TrSymbol then "_I" ++ symbolRes
	    else "_Z_I" ++ symbolRes
    "?"  -> if lss == TrSymbol then "_Q" ++ symbolRes
	    else "_Z_Q" ++ symbolRes
    ":"  -> if lss == TrSymbol then "_C" ++ symbolRes
	    else "_Z_C" ++ symbolRes
    "$"  -> if lss == TrSymbol then "_S" ++ symbolRes
	    else "_Z_S" ++ symbolRes
    "@"  -> if lss == TrSymbol then "_O" ++ symbolRes
	    else "_Z_O" ++ symbolRes
    "#"  -> if lss == TrSymbol then "_H" ++ symbolRes
	    else "_Z_H" ++ symbolRes
    "^"  -> if lss == TrSymbol then "_V" ++ symbolRes
	    else "_Z_V" ++ symbolRes
    "~"  -> if lss == TrSymbol then "_N" ++ symbolRes
	    else "_Z_N" ++ symbolRes

    _    -> --if and (map isAlpha  t) then
	      if (lss == TrLetter || lss == TrAny) then t
	      else "_A" ++ t
	    --else error ("Fix me: unexpected token" ++ show t)
-}

data LSS = TrLetter | TrSpecial | TrSymbol | TrAny
	   deriving (Eq,Show)

translateCompound :: [Id] -> String
--  [      ,      ]
-- _C     _k     _J
translateCompound [] = ""
translateCompound ids = "_C" ++
                        (concat (intersperse "_k" (map translateId ids)))++
                        "_J"

{-substituteUnderlinesInTokens :: [Token] -> [Token]
substituteUnderlinesInTokens tlist = map substituteUnderlinesInToken tlist

substituteUnderlinesInToken :: Token -> Token
substituteUnderlinesInToken t = Token {tokStr = substituteUnderlines (tokStr t),
                                   tokPos = tokPos t}
-}

substituteUnderlines :: String -> String
substituteUnderlines [] = []
substituteUnderlines (x:xs)
  | x == '_' = "_1" ++ substituteUnderlines xs
  | otherwise = (x:(substituteUnderlines xs))

