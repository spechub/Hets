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

-- Positionsangaben in den erzeugten Haskelldatenstrukturen sind
-- grundsätzlich falsch (werden evtl. nicht benötigt)

idToHaskell :: AParser WrapString
idToHaskell = fmap (WrapString . translateId) parseId 

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

translateAna :: Env -> HsModule
--translateAna env = error (show env)
translateAna env = HsModule (SrcLoc "" 1 1) (Module "HasCASLModul") 
		   Nothing -- Maybe[HsExportSpec]
		   []      -- [HsImportDecl]
                   ((translateTypeMap (typeMap env)) ++ 
                    (translateAssumps (assumps env)))   -- [HsDecl]
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
  let hsname = (HsIdent (translateIdWithType UpperId tid))
      srcloc = (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
  in case (typeDefn info) of
       NoTypeDefn ->  -- z.B. bei sorts, was wird daraus?
          [(HsDataDecl srcloc
	               [] -- empty HsContext
	               hsname
		       [] -- [HsName] no type arguments
		       [(HsConDecl srcloc hsname [])]
		       [] -- [HsQName]  (für deriving) woher?
	   )]
       Supertype _ _ _ -> [] -- Was wird daraus in Haskell? -> ignorieren
       DatatypeDefn _ typeargs altDefns -> 
 	  [(HsDataDecl srcloc
	               [] -- empty HsContext
	               hsname
		       (getDataArgs typeargs) -- type arguments
		       (map translateAltDefn altDefns) -- [HsConDecl] 
		       [] -- [HsQName]  (für deriving) woher?
	   )]
       AliasTypeDefn ts -> 
	  [(HsTypeDecl srcloc
	               hsname
	               (getAliasArgs ts)
	               (getAliasType ts)
	   )]
       TypeVarDefn -> [] -- ?

translateAltDefn :: AltDefn -> HsConDecl
translateAltDefn (Construct uid ts _ []) = 
    HsConDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	      (HsIdent (translateIdWithType UpperId uid))
	      (getArgTypes ts)
translateAltDefn (Construct uid _ts _ sel) =
    HsRecDecl (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
	      (HsIdent (translateIdWithType UpperId uid))
	      (translateRecords sel)

translateRecords ::[Selector] -> [([HsName],HsBangType)]
translateRecords = map translateRecord

translateRecord :: Selector -> ([HsName], HsBangType)
translateRecord (Select opid t _) = 
    ([(HsIdent (translateIdWithType LowerId opid))],
     getType t)

getArgTypes :: [Type] -> [HsBangType]
getArgTypes ts = map getType ts

getType :: Type -> HsBangType
getType t = HsUnBangedTy (translateType t)

getDataArgs :: [TypeArg] -> [HsName]
getDataArgs = map getAliasArg
    
getAliasArgs :: TypeScheme -> [HsName]
getAliasArgs (TypeScheme arglist (_plist :=> _t) _poslist) = 
    map getAliasArg arglist

getAliasArg :: TypeArg -> HsName
getAliasArg (TypeArg tid _ _ _) = (HsIdent (translateIdWithType LowerId tid))
-- ist UpperId oder LowerId hier richtig?

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _arglist (_plist :=> t) _poslist) = translateType t
-------------------------------------------------------------------------
-- Translation of functions
-------------------------------------------------------------------------

translateAssumps :: Assumps -> [HsDecl]
translateAssumps m = concat $ map translateAssump (assocs m)

translateAssump :: (Id,[OpInfo]) -> [HsDecl]
translateAssump (_, []) = []
translateAssump (i, (x:xs)) = ((translateSignature i x) ++
                               (translateAssump (i, xs)))

translateSignature :: Id -> OpInfo -> [HsDecl]
translateSignature i opinf = 
  let res = [HsTypeSig (SrcLoc {srcFilename = "", srcLine = 0, srcColumn = 0})
                       [(HsIdent (translateIdWithType LowerId i))]
                       (translateTypeScheme (opType opinf))]
  in case (opDefn opinf) of
    NoOpDefn -> res
    ConstructData _ -> []
    SelectData _ _ -> []
    Definition term -> res ++ 
                       translateTerm term -- Term zu HsFunBind übersetzen!! 
    VarDefn -> res

translateTypeScheme :: TypeScheme -> HsQualType
translateTypeScheme (TypeScheme _arglist (_plist :=> t) _poslist) = 
  HsQualType [] (translateType t)
-- Context aus plist (wird im Moment noch nicht benutzt)
-- arglist beachten (wird an anderer Stelle gemacht; 
--                   evtl. Signatur zu Type -> HsQualType ändern??)

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
	 HsTyVar (HsIdent (translateIdWithType LowerId tid)) -- Upper/LowerId?
      else
         HsTyCon (UnQual (HsIdent (translateIdWithType UpperId tid)))
--Missing: Übersetzung der Kind's    

translateTerm :: Term -> [HsDecl] --HsFunBind
translateTerm t = []

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
translateIdWithType ty (Id tlist idlist _poslist) = 
  let s = translateId (Id tlist idlist _poslist)
  in if ty == UpperId then
        if (isLower $ head $ tokStr $ head tlist) || (head s == '_') then
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
symbolMapping c = findWithDefault [c] c symbolMap

{-symbolMapping :: Char -> String
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
    '='  -> "_I"    -- \61
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
-}

translateCompound :: [Id] -> String
--  [      ,      ]
-- _C     _k     _J
translateCompound [] = ""
translateCompound ids = "_C" ++
                        (concat $ intersperse "_k" $ map translateId ids) ++
                        "_J"

symbolMap :: Map Char String
symbolMap = fromList symbolTable

symbolTable :: [(Char,String)]
symbolTable = 
-- Special / reserviert
   [('_' , "_1"),    -- \95
    ('{' , "_b"),    -- \123
    ('}' , "_r"),    -- \125
    ('[' , "_s"),    -- \91
    (']' , "_q"),    -- \93
    ('.' , "_d"),    -- \46
    ('\'', "_p"),
-- Symbole
    ('+' , "_P"),    -- \43
    ('-' , "_M"),    -- \45
    ('*' , "_T"),    -- \42
    ('/' , "_D"),    -- \47
    ('\\', "_B"),    -- \92
    ('&' , "_A"),    -- \38
    ('=' , "_I"),    -- \61
    ('<' , "_L"),    -- \60
    ('>' , "_G"),    -- \62
    ('!' , "_E"),    -- \33
    ('?' , "_Q"),    -- \63
    (':' , "_C"),    -- \58
    ('$' , "_S"),    -- \36
    ('@' , "_O"),    -- \64
    ('#' , "_H"),    -- \35
    ('^' , "_V"),    -- \94
    ('|' , "_I"),    -- \124
    ('~' , "_N"),    -- \126
    ('¡' , "_e"),    -- \161
    ('¢' , "_c"),    -- \162   
    ('£' , "_l"),    -- \163
    ('§' , "_f"),    -- \167
    ('©' , "_a"),    -- \169
    ('¬' , "_n"),    -- \172
    ('°' , "_h"),    -- \176
    ('±' , "_k"),    -- \177
    ('²' , "_w"),    -- \178
    ('³' , "_t"),    -- \179
    ('µ' , "_y"),    -- \181
    ('¶' , "_j"),    -- \182
    ('·' , "_i"),    -- \183
    ('¹' , "_o"),    -- \185
    ('¿' , "_q"),    -- \191
    ('×' , "_m"),    -- \215
    ('÷' , "_g")]    -- \247
