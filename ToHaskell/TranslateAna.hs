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
       , distinctOpIds
       -- ** Translation of terms
       , translateTerm
       -- ** Translation of pattern
       , translatePattern
       -- * Translation of a map of types
       , translateTypeMap
       , translateData
       -- * Testing
       , idToHaskell
       ) where

import HasCASL.As
import HasCASL.Le
--import HasCASL.Unify
import Haskell.Language.Syntax
import Common.Id
import qualified Common.Lib.Map as Map hiding (map)
import Common.Token
import Common.AnnoState
import Common.PPUtils
import Data.Char
import Data.List
import ToHaskell.TranslateId
import ToHaskell.UniqueId
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

-- | Function for the test of the translation if identifiers.
idToHaskell :: AParser WrapString
idToHaskell = fmap (WrapString . translateId) parseId 

-------------------------------------------------------------------------
-- Translation of an HasCASL-Environement
-------------------------------------------------------------------------

-- | Converts an abstract syntax of HasCASL (after the static analysis) 
-- to the top datatype of the asbtract syntax of haskell.
-- Calls 'translateTypeMap' and 'translateAssumps'.
translateAna :: Env -> HsModule
--translateAna env = error (show env)
translateAna env = 
    HsModule nullLoc (Module "HasCASLModul") 
	     Nothing -- Maybe[HsExportSpec]
	     [(HsImportDecl nullLoc
	                    (Module "Prelude") 
                            False 
	                    Nothing 
		            (Just (False, [HsIVar (HsIdent "undefined")])))]
             ((translateTypeMap (typeMap env)) ++ 
             (translateAssumps (assumps env) (typeMap env)))   -- [HsDecl]
-- Achtung: env enthält noch andere zu übersetzende Argumente 
-- (z.B. classMap, sentences) !!

-------------------------------------------------------------------------
-- Translation of types
-------------------------------------------------------------------------

-- | Converts all HasCASL types to data or type declarations in haskell.
-- Uses 'translateData'.
translateTypeMap :: TypeMap -> [HsDecl]
translateTypeMap m = concat $ map translateData (Map.assocs m)

-- | Converts one type to a data or type declaration in haskell.
-- Uses 'translateIdWithType'.
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
       Supertype vars ty _form -> --evtl so noch nicht richtig
	   [(HsTypeDecl nullLoc
                        hsname
                        (getVars vars)
	                (translateType ty)
	   )]
       --Vars: eine var (= Id) oder Liste von Vars
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

getVars :: Vars -> [HsName]
getVars (Var var) = [HsIdent (translateIdWithType LowerId var)]
getVars (VarTuple varlist _) = concatMap getVars varlist

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
getDataArgs = map getArg
    
getAliasArgs :: TypeScheme -> [HsName]
getAliasArgs (TypeScheme arglist (_plist :=> _t) _poslist) = 
    map getArg arglist

getArg :: TypeArg -> HsName
getArg (TypeArg tid _ _ _) = (HsIdent (translateIdWithType LowerId tid))
-- ist UpperId oder LowerId hier richtig?

getAliasType :: TypeScheme -> HsType
getAliasType (TypeScheme _arglist (_plist :=> t) _poslist) = translateType t


-------------------------------------------------------------------------
-- Translation of functions
-------------------------------------------------------------------------

-- | Converts functions in HasCASL to the coresponding haskell declarations.
translateAssumps :: Assumps -> TypeMap -> [HsDecl]
translateAssumps as tm =
  let distList =  distinctOpIds $ Map.toList as
      distAs = Map.fromList distList
  in  concat $ map (translateAssump distAs tm) $ distList
      --error ("List: " ++ show distList ++ "\n Map: " ++ show distAs)

-- | Converts one distinct named function in HasCASL to the corresponding
-- haskell declaration.
-- Generates a definition (Prelude.undefined) for functions that are not 
-- defined in HasCASL.
translateAssump :: Assumps -> TypeMap -> (Id,OpInfos) -> [HsDecl]
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
translateType t = 
 let err = error ("unexpected type: " ++ show t) in 
  case t of
  FunType t1 _arr t2 _poslist -> HsTyFun (translateType t1) (translateType t2)
  ProductType tlist _poslist -> HsTyTuple (map translateType tlist)
  LazyType lt _poslist -> translateType lt
  MixfixType _ -> err
  KindedType kt _kind _poslist -> translateType kt
  BracketType _ _ _ -> err
  TypeToken _ -> err
  TypeAppl t1 t2 -> HsTyApp (translateType t1) (translateType t2)
  TypeName tid _kind n -> 
      if n > 0 then
	 HsTyVar (HsIdent (translateIdWithType LowerId tid)) -- Upper/LowerId?
      else
         HsTyCon (UnQual (HsIdent (translateIdWithType UpperId tid)))   

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


-- |Converts a term in HasCASL to an expression in haskell
translateTerm :: Assumps -> TypeMap -> Term -> HsExp --HsFunBind
translateTerm as tm t = 
  let err = error ("Unexpected term: " ++ show t) in
  case t of
    --CondTerm _t1 _form _t2 _pos -> 
	--error ("CondTerm not yet translated" ++ show t)
    --HsIf HsExp HsExp HsExp, wie passt das zusammen?

    QualVar v ty _pos ->
        (HsExpTypeSig 
          nullLoc 
          (HsVar (UnQual (HsIdent (translateIdWithType LowerId v))))
          (HsQualType [] $ translateType ty))
      
    -- zur id der opid muss der evtl. umbenannte eindeutige Name gefunden 
    -- werden; hierzu muss ts mit den TypeSchemes aus Assumps auf 
    -- Unifizierbarkeit geprueft werden; 
    -- hierzu benoetigt man die Assumps und die TypeMap;
    QualOp (InstOpId uid types _) ts _pos -> 
    -- zunaechst alle TypeSchemes aus den Assumps mit dem gegebenen 
    -- vergleichen, bei passendem TypeScheme die id (also den Schluessel) 
    -- als HsVar verwenden
      let oid = findUniqueId uid ts tm as 
      in case oid of
            Just i ->
		(HsVar (UnQual (HsIdent (translateIdWithType LowerId i))))
	    _ -> error("problem with finding opid: " ++ show uid ++ "\n" 
                     ++ show ts ++ "\n" ++ show types)

    ApplTerm t1 t2 _pos ->
	HsApp(translateTerm as tm t1)(translateTerm as tm t2)
    TupleTerm ts _pos -> HsTuple (map (translateTerm as tm) ts)
    TypedTerm t1 tqual ty _pos ->
      let res = (HsExpTypeSig nullLoc 
	                    (translateTerm as tm t1)
                            (HsQualType [] $ translateType ty)) in
      case tqual of 
        OfType -> res
        --AsType -> (HsFunBind [HsMatch nullLoc (HsIdent "unsafeCoerce") ....
        --hier können nur HsExp berechnet werden,evtl. muss an einer "höheren"
        --Stelle der Funktionsaufruf der Cast-funktion gebastelt werden;
        --bei AsType könnte t1::ty reichen, da Subtypen als Typsynonyme
        --übersetzt werden
        AsType -> res
        InType -> error ("Translation of \"InType\" not possible: " ++ show t)

    QuantifiedTerm _quant _vars _t1 _pos -> -- forall ... ?
        error ("Translation of QuantifiedTerm not possible" ++ show t)
    LambdaTerm pats _part t1 _pos -> 
        HsLambda nullLoc
                 (map (translatePattern tm as) pats)
	         (translateTerm as tm t1)

    CaseTerm t1 progeqs _pos -> 
        HsCase (translateTerm as tm t1) (translateCaseProgEqs progeqs)

    LetTerm progeqs t1 _pos -> 
        HsLet (translateProgEqs progeqs) (translateTerm as tm t1)

    TermToken _ttok -> err
    MixfixTerm _ts -> err
    BracketTerm _ _ _ -> err

--Uebersetzung der Liste von Pattern aus HasCASL-Lambdaterm
-- | Conversion of patterns form HasCASL to haskell.
translatePattern :: TypeMap -> Assumps -> Pattern -> HsPat
translatePattern tm as pat = 
  let err = error ("unexpected pattern: " ++ show pat) in
    case pat of
      PatternVar (VarDecl v _ty _sepki _pos) 
	  -> HsPVar $ HsIdent $ translateIdWithType LowerId v
      --PatternConstr .... -> HsPRec HsQname [HsPatField]
      PatternConstr (InstOpId uid _t _p) ts pats _pos -> 
        let oid = findUniqueId uid ts tm as
	in case oid of
	     Just i -> 
		 HsPApp (UnQual $ HsIdent $ translateIdWithType LowerId i)
	                (map (translatePattern tm as) pats)
	     _ -> error ("Proplem with finding of unique id" ++ show pat)
      PatternToken _ -> err
      BracketPattern _ _ _ -> err
      TuplePattern pats _pos -> HsPTuple $ map (translatePattern tm as) pats
      MixfixPattern _ -> err
      TypedPattern p _ty _pos -> translatePattern tm as p --Typ evtl implizit
      --AsPattern pattern pattern pos -> HsPAsPat name pattern ??
      AsPattern _p1 _p2 _pos -> error "AsPattern nyi"

-- Uebersetzung der ProgEqs fuer einen HasCASL-Caseterm
translateCaseProgEqs :: [ProgEq] -> [HsAlt]
translateCaseProgEqs _progeqs = []

--translateCaseProgEq :: ProgEq -> HsAlt
--translateCaseProgEq (ProgEq pat t _pos) = error "nyi"

--Uebersetzung der ProgEqs fuer einen HasCASL-Letterm
translateProgEqs :: [ProgEq] -> [HsDecl]
translateProgEqs _progeqs = []

