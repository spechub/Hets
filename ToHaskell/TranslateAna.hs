{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   Translation of the abstract syntax of HasCASL after the static analysis
   to the abstract syntax of haskell.
-}

module ToHaskell.TranslateAna (
       -- * Translation of an environment
         translateAna
       -- * Translation of a map of assumptions
       , translateAssumps
       -- * Translation of a map of types
       , translateTypeMap
       ) where

import HasCASL.As
import HasCASL.Le
import HasCASL.Unify
import Haskell.Language.Syntax
import Common.Id
import qualified Common.Lib.Map as Map hiding (map)
import Common.Token
import Common.AnnoState
import Common.PPUtils
import Data.Char
import Data.List
-------------------------------------------------------------------------
-- einige "Konstanten"
-------------------------------------------------------------------------

-- Positionsangaben in den erzeugten Haskelldatenstrukturen sind
-- grundsätzlich falsch (werden evtl. nicht benötigt)
nullLoc :: SrcLoc
nullLoc = SrcLoc "" 1 1

-- undefinierte Funktion, erwartet den Funktionsnamen als Parameter
functionUndef :: String -> HsDecl
functionUndef s = 
    HsPatBind nullLoc
	      (HsPVar (HsIdent s))
	      (HsUnGuardedRhs (HsVar (UnQual (HsIdent "undefined"))))
	      []

-------------------------------------------------------------------------
-- Funktion zum Aufruf des Parsers fuer ID's
-------------------------------------------------------------------------

idToHaskell :: AParser WrapString
idToHaskell = fmap (WrapString . translateId) parseId 

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

-- | Convert an abstract syntax of HasCASL (after the static analysis) 
-- to the top datatype of the asbtract syntax of haskell.
translateAna :: Env -> HsModule
--translateAna env = error (show env)
translateAna env = 
    HsModule nullLoc (Module "HasCASLModul") 
	     Nothing -- Maybe[HsExportSpec]
	     [(HsImportDecl nullLoc
	                    (Module "Prelude") 
                            False 
	                    Nothing 
		            (Just (False,[HsIVar (HsIdent "undefined")])))]
             ((translateTypeMap (typeMap env)) ++ 
             (translateAssumps (assumps env) (typeMap env)))   -- [HsDecl]
-- Achtung: env enthält noch andere zu übersetzende Argumente 
-- (z.B. classMap, sentences) !!

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

-- | Convert all HasCASL types to data or type declarations in haskell.
translateTypeMap :: TypeMap -> [HsDecl]
translateTypeMap m = concat $ map translateData (Map.assocs m)

-- muss translateData eine Liste von HsDecl's oder eine HsDecl liefern?
translateData :: (TypeId, TypeInfo) -> [HsDecl]
translateData (tid,info) = 
  let hsname = (HsIdent (translateIdWithType UpperId tid))
  in case (typeDefn info) of
       NoTypeDefn ->  -- z.B. bei sorts
          [(HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       [] -- [HsName] no type arguments
		       [(HsConDecl nullLoc hsname [])]
		       [] -- [HsQName]  (für deriving) woher?
	   )]
       Supertype _ _ _ -> [] -- Was wird daraus in Haskell? -> ignorieren
       DatatypeDefn _ typeargs altDefns -> 
 	  [(HsDataDecl nullLoc
	               [] -- empty HsContext
	               hsname
		       (getDataArgs typeargs) -- type arguments
		       (map translateAltDefn altDefns) -- [HsConDecl] 
		       [] -- [HsQName]  (für deriving) woher?
	   )]
       AliasTypeDefn ts -> 
	  [(HsTypeDecl nullLoc
	               hsname
	               (getAliasArgs ts)
	               (getAliasType ts)
	   )]
       TypeVarDefn -> [] -- werden in Haskell ignoriert

translateAltDefn :: AltDefn -> HsConDecl
translateAltDefn (Construct uid ts _ []) = 
    HsConDecl nullLoc
	      (HsIdent (translateIdWithType UpperId uid))
	      (getArgTypes ts)
translateAltDefn (Construct uid _ts _ sel) =
    HsRecDecl nullLoc
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
getType t = HsBangedTy (translateType t)

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

-- | Convert functions in HasCASL to the coresponding haskell declarations.
translateAssumps :: Assumps -> TypeMap -> [HsDecl]
translateAssumps as tm =
  let distList =  distinctOpIds $ Map.toList as
      distAs = Map.fromList distList
  in  concat $ map (translateAssump distAs tm) $ distList
      --error ("List: " ++ show distList ++ "\n Map: " ++ show distAs)

-- Funktion, die evtl. überladenen Operationen eindeutige Namen gibt
distinctOpIds :: [(Id,OpInfos)] -> [(DistinctOpId, OpInfos)]
distinctOpIds [] = []
distinctOpIds ((i,OpInfos info):(idInfoList)) = 
  let len = length info in
  if len == 0 then
     distinctOpIds idInfoList
  else 
     if len == 1 then
        ((i,OpInfos info):(distinctOpIds (idInfoList)))
     else -- if len > 1
        ((newName i len,OpInfos $ [head info]):
         (distinctOpIds((i, OpInfos $ tail info):(idInfoList))))

-- Durchnummerierung von überladenen Funktionsnamen
newName :: Id -> Int -> Id
newName (Id tlist idlist poslist) len = 
  let newTok = (Token (show len) nullPos) 
  in (Id (tlist ++ [newTok]) idlist poslist)

-- uebersetzt eindeutig benannte Funktionen 
-- (d.h. OpInfos enthält nur ein Element)
-- (Funktionsdeklarationen und -definitionen)
translateAssump :: Assumps -> TypeMap -> (DistinctOpId,OpInfos) -> [HsDecl]
translateAssump as tm (i, opinf) = 
  let fname = translateIdWithType LowerId i
      res = HsTypeSig nullLoc
                       [(HsIdent fname)]
                       (translateTypeScheme (opType $ head $ opInfos opinf))
  in case (opDefn $ head $ opInfos opinf) of
    NoOpDefn -> [res, (functionUndef fname)]
    ConstructData _ -> []  -- sind implizit durch Datentypdefinition gegeben
    SelectData _ _ -> []   -- sind implizit durch Datentypdefinition gegeben
    Definition term -> 
      (translateFunDef as tm i (opType $ head $ opInfos opinf) term)
                        -- zu HsFunBind übersetzen!! 
    VarDefn -> []

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
  -- TypeToken ttok -> HsTyCon (UnQual (HsIdent (tokStr ttok)))
  TypeToken _ -> error ("unexpected type (TypeToken): " ++ show t)
  TypeAppl t1 t2 -> HsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> 
      if n > 0 then
	 HsTyVar (HsIdent (translateIdWithType LowerId tid)) -- Upper/LowerId?
      else
         HsTyCon (UnQual (HsIdent (translateIdWithType UpperId tid)))
--Missing: Übersetzung der Kind's    

-- translateFunDef liefert idealerweise eine HsTypSig und ein HsFunBind
translateFunDef :: Assumps -> TypeMap -> Id -> TypeScheme -> Term -> [HsDecl]
--translateFunDef as tm i ts term = error ("Typescheme: " ++ show ts ++ "\n Term: " ++ show term)
translateFunDef as tm i ts term = 
  let fname = translateIdWithType LowerId i
  in [HsTypeSig nullLoc 
             [(HsIdent fname)] 
              (translateTypeScheme ts)] ++
     [HsFunBind [HsMatch nullLoc
	             (HsIdent fname) --HsName
	             (getPattern term) -- [HsPat]
	             (getRhs as tm term) -- HsRhs
	             [] -- {-where-} [HsDecl]
	       ]
     ]


getPattern :: Term -> [HsPat]
getPattern _t = []

getRhs :: Assumps -> TypeMap -> Term -> HsRhs
getRhs as tm t = HsUnGuardedRhs (translateTerm as tm t) 

translateTerm :: Assumps -> TypeMap -> Term -> HsExp --HsFunBind
translateTerm as tm t = case t of
  --CondTerm _t1 _form _t2 _pos -> [] -- -> HsIf
  --HsIf HsExp HsExp HsExp, wie passt das zusammen?

  QualVar v ty _pos ->
      (HsExpTypeSig 
        nullLoc 
        (HsVar (UnQual (HsIdent (translateIdWithType LowerId v))))
        (HsQualType [] $ translateType ty))

  -- zur id der opid muss der evtl. umbenannte eindeutige Name gefunden werden
  -- hierzu muss ts mit den TypeSchemes aus Assumps auf Unifizierbarkeit
  -- geprueft werden; hierzu benoetigt man die Assumps und die TypeMap;
  QualOp (InstOpId uid types _) ts _pos -> 
  -- zunaechst alle TypeSchemes aus den Assumps mit dem gegebenen vergleichen,
  -- bei passendem TupeScheme die id (also den Schluessel) als HsVar verwenden
    let fittingAs = Map.filter (canUnify tm ts) as 
    in if Map.size fittingAs == 1 then
         -- gut, eine Uebereinstimmung
          let oid = head $ Map.keys $ fittingAs
          in (HsVar (UnQual (HsIdent (translateIdWithType LowerId oid))))
       else
          if Map.size fittingAs > 1 then
          --falls mehr als ein passendes TypeScheme gefunden wurde
          --kann auf "Ähnlichkeit" mit der Id getestet werden
            let oid = head $ Map.keys $ fittingAs
            in (HsVar (UnQual (HsIdent (translateIdWithType LowerId oid))))
          else error("problem with finding opid: " ++ show uid ++ "\n" 
                     ++ show ts ++ "\n" ++ show types ++ "\n" ++ 
                     show (Map.size fittingAs))

  ApplTerm t1 t2 _pos -> HsApp(translateTerm as tm t1)(translateTerm as tm t2)
  TupleTerm ts _pos -> HsTuple (map (translateTerm as tm) ts)
  TypedTerm t1 tqual ty _pos -> -- -> HsExpTypeSig
    case tqual of 
      OfType -> (HsExpTypeSig nullLoc 
	                     (translateTerm as tm t1)
                             (HsQualType [] $ translateType ty))
      --AsType ->
      --InType ->
      _ -> error "TypedTerm not yet finished"

  --QuantifiedTerm _quant _vars _t1 _pos -> [] -- forall ... ?

  LambdaTerm pats _part t1 _pos -> 
      HsLambda nullLoc
               (translatePattern pats)
	       (translateTerm as tm t1)

  CaseTerm t1 progeqs _pos -> 
      HsCase (translateTerm as tm t1) (translateCaseProgEqs progeqs)

  LetTerm progeqs t1 _pos -> 
      HsLet (translateProgEqs progeqs) (translateTerm as tm t1)

  TermToken _ttok -> error ("unexpected term (TermToken): " ++ show t)
  MixfixTerm _ts -> error ("unexpected term (MixfixTerm): " ++ show t)
  BracketTerm _ _ _ -> error ("unexpected term (BracketTerm): " ++ show t)
  _ -> error ("translateTerm not finished; Term: " ++ show t)

findTypeSchemeMap :: Assumps -> TypeScheme -> [Id]
findTypeSchemeMap as ts = findTypeSchemeList (Map.toList as) ts

-- hier wird mit einer eindeutigen Benennung der Ids gearbeitet,
-- daher enthält OpInfos jeweils nur ein OpInfo
findTypeSchemeList :: [(UninstOpId,OpInfos)] -> TypeScheme -> [Id]
findTypeSchemeList [] _ts = []
findTypeSchemeList ((id1,infos):idInfoList) ts = 
  if (opType $ head $ opInfos infos) == ts then
    ((id1):(findTypeSchemeList idInfoList ts))
  else findTypeSchemeList idInfoList ts

isEqualTs :: TypeScheme -> TypeScheme -> Bool
isEqualTs (TypeScheme _ (_ :=> t1) _) (TypeScheme _ (_ :=> t2) _) = t1 == t2

canUnify :: TypeMap -> TypeScheme -> OpInfos -> Bool
canUnify tm ts (OpInfos infos) = 
    or $ map (isUnifiable tm 0 ts) (map opType infos)

--Uebersetzung der Liste von Pattern aus HasCASL-Lambdaterm
translatePattern :: [Pattern] -> [HsPat]
translatePattern _pats = []

-- Uebersetzung der ProgEqs fuer einen HasCASL-Caseterm
translateCaseProgEqs :: [ProgEq] -> [HsAlt]
translateCaseProgEqs _progeqs = []

--Uebersetzung der ProgEqs fuer einen HasCASL-Letterm
translateProgEqs :: [ProgEq] -> [HsDecl]
translateProgEqs _progeqs = []

------------------------------------------------------------------------
-- Translation of Id's
------------------------------------------------------------------------

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
symbolMapping c = Map.findWithDefault [c] c symbolMap

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

symbolMap :: Map.Map Char String
symbolMap = Map.fromList symbolTable

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


type DistinctOpId = Id
