{-------------------------------------------------------------------------------

        Copyright:              Mark Jones and The Hatchet Team 
                                (see file Contributors)

        Module:                 Class

        Description:            Code for manipulating the class hierarchy and 
                                qualified types.

                                The main tasks implemented by this module are:
                                        - context reduction
                                        - context spliting
                                        - defaulting
                                        - entailment of class constraints
                                        - class hierarchy representation and
                                          manipulation

        Primary Authors:        Mark Jones, Bernie Pope

        Notes:                  See the files License and License.thih 
                                for license information.

                                Large parts of this module were derived from
                                the work of Mark Jones' "Typing Haskell in
                                Haskell", (http://www.cse.ogi.edu/~mpj/thih/)

-------------------------------------------------------------------------------}

module Class          (addClassToHierarchy,
                       emptyClassHierarchy,
                       -- addInstancesToHierarchy,
                       printClassHierarchy,
                       -- instanceToTopDecls,
                       entails,
                       bySuper,
                       reducePred,
                       classMethodAssumps,
                       ClassHierarchy,
                       reduce,
                       split,
                       useDefaults, 
                       topDefaults
                       ) where

import List                     (union,
                                (\\), 
                                partition)

import Env                      (Env,
                                 emptyEnv,
                                 lookupEnv,
                                 addToEnv,
                                 joinEnv,
                                 joinListEnvs,
                                 listToEnv,
                                 envToList,
                                 showEnv)

import AnnotatedHsSyn           (AHsDecl (..),
                                 AHsType (..),
                                 AHsQualType (..),
                                 AHsContext,
                                 AHsName (..),
                                 AHsIdentifier (..),
                                 AHsMatch (..),
                                 AModule (AModule),
                                 bogusASrcLoc,
                                 AHsPat (..))

import Utils                    (showListAndSep,
                                 isSigDecl,
                                 fromAHsName,
                                 qualifyName,
                                 nameOfTyCon,
                                 trd3,
                                 groupEquations,
                                 showListAndSepInWidth,
                                 spacesToUnderscores)

import KindInference            (KindEnv,
                                 kindOf)

import TypeSynonyms             (oneTypeReplace)

import TypeUtils                (aHsAsstToPred,
                                 flattenLeftTypeApplication,
                                 aHsTypeSigToAssumps) 

import Representation           (Type (..),
                                 Tycon (..),
                                 Tyvar (..),
                                 Kind (..),
                                 unfoldKind,
                                 Qual (..),
                                 Pred (..),
                                 Class,
                                 Inst,
                                 Assump (..),
                                 Subst,
                                 prettyPrintInst)

import Type                     (Types (..),
                                 apply,
                                 match)

import PPrint                   (pretty,
                                 PPrint (..),
                                 text,
                                 render,
                                 (<+>),
                                 nest,
                                 ($$))

import HsPretty                 (ppHsDecl,
                                 renderWithMode)

import FiniteMaps               (listToFM)

--------------------------------------------------------------------------------

bySuper :: ClassHierarchy -> Pred -> [Pred]
bySuper h p@(IsIn c t)
 = p : concat (map (bySuper h) supers)
   where supers = [ IsIn c' t | c' <- supersOf h c ]

byInst             :: Pred -> Inst -> Maybe [Pred]
byInst p (ps :=> h) = do u <- matchPred h p
                         Just (map (apply u) ps)

matchPred :: Pred -> Pred -> Maybe Subst
matchPred (IsIn c t) (IsIn c' t')
      | c == c'   = match t t'
      | otherwise = Nothing

reducePred :: ClassHierarchy -> Pred -> Maybe [Pred]
reducePred h p@(IsIn c t) = foldr (|||) Nothing poss
 where poss = map (byInst p) (instsOf h c)
       Nothing ||| y = y
       Just x  ||| y = Just x

-----------------------------------------------------------------------------

entails :: ClassHierarchy -> [Pred] -> Pred -> Bool
entails h ps p = any (p `elem`) (map (bySuper h) ps) ||
           case reducePred h p of
             Nothing -> False
             Just qs -> all (entails h ps) qs

-----------------------------------------------------------------------------

-- the new class hierarchy


-- classname (superclasses, instances, properly qualified type-sigs of methods)

type ClassRecord = ([Class], [Inst], [Assump])
type ClassHierarchy = Env ClassRecord

supersOf :: ClassHierarchy -> Class -> [Class]
supersOf hierarchy className
   = case lookupEnv className hierarchy of
  
        Nothing -> error $ "supersOf: could not find class : " ++ show className ++ " in hierarchy"
        Just (supers, _insts, _methodSigs) -> supers

instsOf :: ClassHierarchy -> Class -> [Inst]
instsOf hierarchy className 
   = case lookupEnv className hierarchy of
   
        Nothing -> error $ "instsOf: could not find class : " ++ show className ++ " in hierarchy"
        Just (_supers, insts, _methodSigs) -> insts

methodSigsOf :: ClassHierarchy -> Class -> [Assump]
methodSigsOf hierarchy className 
   = case lookupEnv className hierarchy of
        Nothing -> error $ "methodSigsOf: could not find class : " ++ show className ++ " in hierarchy"
        Just (_supers, _insts, methodSigs) -> methodSigs
  

showInst :: Inst -> String 
{-
showInst ([] :=> IsIn c t)
   = pretty t
showInst (quals@(_:_) :=> IsIn c t)
   = prettyAQuals quals ++ " => " ++ pretty t 
   where
   prettyAQuals qs
      = "(" ++ showListAndSep showPred ", " qs ++ ")"
-}
showInst = PPrint.render . prettyPrintInst 
        
showPred :: Pred -> String
showPred (IsIn c t)
   = show c ++ " " ++ (pretty t)

makeDeriveInstances :: [Pred] -> Type -> [Class] -> [Inst]
makeDeriveInstances context t [] = []
makeDeriveInstances context t (c:cs)
   | c `elem` deriveableClasses
        = (context :=> IsIn c t) : makeDeriveInstances context t cs
   | otherwise
        = error $ "makeDeriveInstances: attempt to make type " ++ pretty t ++
                  "\nan instance of a non-deriveable class " ++ show c

-- XXX bjpop: this should really go somewhere else
deriveableClasses :: [Class]
deriveableClasses = [AQual (AModule "Prelude") (AHsIdent "Eq"), 
                     AQual (AModule "Prelude") (AHsIdent "Ord"), 
                     AQual (AModule "Prelude") (AHsIdent "Enum"), 
                     AQual (AModule "Prelude") (AHsIdent "Bounded"), 
                     AQual (AModule "Prelude") (AHsIdent "Show"), 
                     AQual (AModule "Prelude") (AHsIdent "Read"), 
                     AQual (AModule "Prelude") (AHsIdent "Ix")]


emptyClassHierarchy :: ClassHierarchy
emptyClassHierarchy = emptyEnv 

addClassToHierarchy :: AModule -> KindEnv -> AHsDecl -> ClassHierarchy -> ClassHierarchy
addClassToHierarchy mod kt (AHsClassDecl _sloc (AHsQualType cntxt (AHsTyApp (AHsTyCon className) (AHsTyVar argName))) decls) h
   = addToEnv (className, (supers, [], qualifiedMethodAssumps)) h  
   where 
   supers = map fst cntxt
   qualifiedMethodAssumps
      = concatMap (aHsTypeSigToAssumps kt . qualifyMethod newClassContext) (filter isSigDecl decls)
   newClassContext
      = [(className, argName)] 


addClassToHierarchy mod kt (AHsClassDecl _sloc (AHsUnQualType (AHsTyApp (AHsTyCon className) (AHsTyVar argName))) decls) h
   = addToEnv (className, ([], [], qualifiedMethodAssumps)) h
   where
   qualifiedMethodAssumps
      = concatMap (aHsTypeSigToAssumps kt . qualifyMethod newClassContext) (filter isSigDecl decls) 
   newClassContext
      = [(className, argName)] 

qualifyMethod :: AHsContext -> (AHsDecl) -> (AHsDecl)
qualifyMethod cntxt (AHsTypeSig sloc names (AHsUnQualType t))
   = AHsTypeSig sloc names (AHsQualType cntxt t)
qualifyMethod newCntxt (AHsTypeSig sloc names (AHsQualType oldContext t))
   = AHsTypeSig sloc names (AHsQualType (newCntxt++oldContext) t)


printClassHierarchy :: ClassHierarchy -> IO ()
printClassHierarchy h
   = mapM_ printClassDetails $  envToList h
   where
   printClassDetails :: (AHsName, ([AHsName], [Inst], [Assump])) -> IO ()
   printClassDetails (cname, (supers, insts, methodAssumps))
      = do
            putStrLn "..........."
            putStrLn $ "\nclass: " ++ show cname
            putStr $ "\nsuper classes:"
            case supers of
               [] -> putStrLn $ " none"
               _  -> putStrLn $ " " ++ (showListAndSep id " " (map show supers))
            putStr $ "\ninstances:"
            case insts of
               [] -> putStrLn $ " none"
               _  -> putStrLn $ "\n" ++ (showListAndSepInWidth showInst 80 ", " insts)
            putStr $ "\nmethod signatures:"
            case methodAssumps of
            
               [] -> putStrLn $ " none"
               _  -> putStrLn $ "\n" ++ 
                        (unlines $ map pretty methodAssumps)
            
         
            putStr "\n"

{-
genClassHierarchy :: [(AHsDecl)] -> ClassHierarchy 
genClassHierarchy classes 
   = foldl (flip addClassToHierarchy) stdClassHierarchy classes 
   where
   -- stdClassHierarchy = classListToHierarchy stdClasses
   stdClassHierarchy = listToFM preludeClasses 
-}

--------------------------------------------------------------------------------

{-
addInstancesToHierarchy :: KindEnv -> ClassHierarchy -> [HsDecl] -> ClassHierarchy
addInstancesToHierarchy kt ch decls
   = foldl addOneInstanceToHierarchy ch instances 
   where 
   instances = concatMap (hsInstDeclToInst kt) decls


addOneInstanceToHierarchy :: ClassHierarchy -> Inst -> ClassHierarchy
addOneInstanceToHierarchy ch inst@(cntxt :=> IsIn className _) 
   = newHierarchy
   where
   newHierarchy
      -- check to make sure the class exists
      -- = case lookupFM ch className of
      = case lookupEnv className ch f
           Nothing
              -> error $ "addInstanceToHierarchy: attempt to add instance decl: " ++ showInst inst ++
                         ", to non-existent class: " ++ show className
           Just _ -> addToCombFM nodeCombiner className newElement ch
   newElement = ([], [inst], [])
   nodeCombiner :: ([HsName], [Inst], [Assump]) -> ([HsName], [Inst], [Assump]) -> ([HsName], [Inst], [Assump])
   nodeCombiner (_, [newInst], _) (supers, oldInsts, oldMethodSigs) = (supers, newInst:oldInsts, oldMethodSigs)
-}

{-

from section 4.3.2 of the Haskell 98 report

instance decls look like:
   instance cx' => C (T u1 ... uk) where { d }

where u_i are simple variables and are distinct

XXX
currently hsInstDeclToInst does not check whether the context of
an instance declaration is legal, for example it allows:

instance (Eq a, Functor a) => Eq (Tree a) where ...
 the kind of Functor, and Eq are different (the Functor is wrong here)

-}

hsInstDeclToInst :: KindEnv -> (AHsDecl) -> [Inst]
hsInstDeclToInst kt (AHsInstDecl _sloc qType _decls)
   | classKind == argTypeKind
        = [cntxt :=> IsIn className convertedArgType]
   | otherwise
        = error $ "hsInstDeclToInst: kind error, attempt to make\n" ++
                  show argType ++ " (with kind " ++
                  show argTypeKind ++ ")\n" ++
                  "an instance of class " ++ show className ++
                  " (with kind " ++ show classKind ++ ")"
   where
   (cntxt, classType, argType) 
      = case qType of
           AHsQualType context (AHsTyApp cType@(AHsTyCon _) aType)
              -> (map (aHsAsstToPred kt) context, cType, aType)
           AHsUnQualType (AHsTyApp cType@(AHsTyCon _) aType)
              -> ([],  cType, aType)
   {- 
      Note:
      kind (Either) = *->*->*
      kind (Either a) = *->*
      kind (Either a b) = *

      the kind of the argument type (argTypeKind) is the remaining
      kind after droping the kinds of the supplied arguments from
      the kind of the type constructor
   -}
   argTypeKind :: Kind
   convertedArgType :: Type
   (argTypeKind, convertedArgType)
      = case argType of
           AHsTyTuple args -> (Star, TTuple $ map toType $ zip args $ repeat Star)
           _anythingElse 
              -> let tyConName = nameOfTyCon tyCon 
                     numArgs = (length flatType) - 1
                     flatType = flattenLeftTypeApplication argType
                     flatTyConKind = unfoldKind tyConKind
                     tyConKind = kindOf tyConName kt
                     tyCon = head flatType
                     typeKindPairs = (tyCon, tyConKind) : (zip (tail flatType) flatTyConKind)
                     in (foldr1 Kfun $ drop numArgs flatTyConKind,
                         convType typeKindPairs)
   className = nameOfTyCon classType
   classKind = kindOf className kt

-- derive statements
hsInstDeclToInst kt (AHsDataDecl _sloc cntxt tyConName argNames _condecls derives@(_:_)) 
   = newInstances
   where
   tyConKind = kindOf tyConName kt 
   flatTyConKind = unfoldKind tyConKind
   argTypeKind = foldr1 Kfun $ drop (length argNames) flatTyConKind 
   argsAsTypeList = map (\n -> AHsTyVar n) argNames
   typeKindPairs :: [(AHsType, Kind)]
   typeKindPairs = (AHsTyCon tyConName, tyConKind) : zip argsAsTypeList flatTyConKind
   convertedType :: Type
   convertedType = convType typeKindPairs
   newContext = map (aHsAsstToPred kt) cntxt
   newInstances = makeDeriveInstances newContext convertedType derives 

hsInstDeclToInst _kt (AHsDataDecl _sloc _cntxt _tyConName _argNames _condecls emptyDerives@[]) 
   = []

-- the types will only ever be constructors or vars

convType :: [(AHsType, Kind)] -> Type
convType tsks
   = foldl1 TAp (map toType tsks)

toType :: (AHsType, Kind) -> Type
toType (AHsTyCon n, k) = TCon $ Tycon n k
toType (AHsTyVar n, k) = TVar $ Tyvar n k

{-
makeDeriveInstances :: [Pred] -> Type -> [Class] -> [Inst]
makeDeriveInstances context t [] = []
makeDeriveInstances context t (c:cs)
   | c `elem` deriveableClasses
        = (context :=> IsIn c t) : makeDeriveInstances context t cs
   | otherwise
        = error $ "makeDeriveInstances: attempt to make type " ++ pretty t ++ 
                  "\nan instance of a non-deriveable class " ++ c
-}

-- as defined by section 4.3.3 of the haskell report
{-
deriveableClasses :: [Class]
deriveableClasses = ["Eq", "Ord", "Enum", "Bounded", "Show", "Read"]
-}

{-

   converts leftmost type applications into lists

   (((TC v1) v2) v3) => [TC, v1, v2, v3]

-}

 
--------------------------------------------------------------------------------

-- code for making instance methods into top level decls
-- by adding a (instantiated) type signature from the corresponding class
-- decl


{-

instanceToTopDecls :: ClassHierarchy -> HsDecl -> [HsDecl]
instanceToTopDecls classHierarchy (HsInstDecl _sloc qualType methods)
   = concatMap (methodToTopDecls methodSigs qualType) methodGroups
   where
   className 
      = case qualType of
           HsAQualType _cntxt (HsTyApp (HsTyCon className) _argType) -> className
           HsUnAQualType (HsTyApp (HsTyCon className) _argType) -> className 
   
   methodGroups = groupEquations methods
   methodSigs 
      = case lookupFM classHierarchy (fromHsName className) of
           Nothing 
              -> error $ "instanceToTopDecls: could not find class " ++ fromHsName className ++ "in class hierarchy"
           Just (_supers, _insts, sigs) -> sigs




methodToTopDecls :: [HsDecl] -> HsAQualType -> (HsName, [HsDecl]) -> [HsDecl]

methodToTopDecls methodSigs qType (methodName, methodDecls)
    = instantiatedSig : renamedMethodDecls
    where
    (cntxt, classApp)
       = case qType of
            HsAQualType c t -> (c,  t)
            HsUnAQualType t -> ([], t) 
    (HsTyApp (HsTyCon className) argType) = classApp
    -- newMethodName should be something like: 
    --    "_show_Maybe_a"
    --    "_read_Either_a_b"
    newMethodName 
       = UnAQual $ "_" ++ 
                     fromHsName methodName ++ 
                     "_" ++ 
                     (spacesToUnderscores $ showHsType $ argType)
    sigFromClass = findMethodSig methodName methodSigs 
    instantiatedSig
       = newMethodSig cntxt newMethodName sigFromClass argType
    renamedMethodDecls
       = map (renameOneDecl newMethodName) methodDecls

renameOneDecl :: HsName -> HsDecl -> HsDecl
renameOneDecl newName (HsFunBind sloc matches)
   = HsFunBind sloc (map (renameOneMatch newName) matches)
-- all pattern bindings are simple by this stage
-- (ie no compound patterns)
renameOneDecl newName (HsPatBind sloc (HsPVar patName) rhs wheres)
   = HsPatBind sloc (HsPVar newName) rhs wheres

renameOneMatch :: HsName -> HsMatch -> HsMatch
renameOneMatch newName (HsMatch sloc oldName pats rhs wheres)
   = HsMatch sloc newName pats rhs wheres


findMethodSig :: HsName -> [HsDecl] -> HsDecl
findMethodSig name []
   = error $ "findMethodSig: could not find type signature for the class method: " ++ show name
findMethodSig name ((HsTypeSig _sloc names qualType):sigs)
   | name `elem` names 
        = HsTypeSig bogusSrcLoc [name] qualType
   | otherwise = findMethodSig name sigs 

newMethodSig :: HsContext -> HsName -> HsDecl -> HsType -> HsDecl
newMethodSig newCntxt newName (HsTypeSig _sloc methodName (HsAQualType cntxt t)) instanceType
   = HsTypeSig bogusSrcLoc [newName] newAQualType 
   where
   -- the assumption is that the context is non-empty and that
   -- the class and variable that we are interested in are at the
   -- front of the old context - the method of inserting instance types into
   -- the class hierarchy should ensure this
   ((className, classArg):restContxt) = cntxt
   newT = oneTypeReplace (HsTyVar classArg, instanceType) t 
   newAQualType 
      = let finalCntxt = newCntxt++restContxt 
           in case finalCntxt of
                 []    -> HsUnAQualType newT
                 (_:_) -> HsAQualType finalCntxt newT 
-}

-- collect assumptions of all class methods 

classMethodAssumps :: ClassHierarchy -> [Assump]
classMethodAssumps hierarchy 
   = allMethodSigs
   where
   allMethodSigs :: [Assump] 
   allMethodSigs = concatMap (trd3.snd) $ envToList hierarchy 

--------------------------------------------------------------------------------

-- context reduction

reduce :: ClassHierarchy -> [Tyvar] -> [Tyvar] -> [Pred] -> ([Pred], [Pred])

reduce h fs gs ps = (ds,rs')
 where (ds, rs) = split h fs ps
       rs'      = useDefaults h (fs++gs) rs

--------------------------------------------------------------------------------

-- context splitting

split       :: ClassHierarchy -> [Tyvar] -> [Pred] -> ([Pred], [Pred])
split h fs ps  
   = partition (all (`elem` fs) . tv) $ 
     simplify h [] $ 
     toHnfs h ps

toHnfs      :: ClassHierarchy -> [Pred] -> [Pred]
toHnfs h = concat . map (toHnf h)

toHnf       :: ClassHierarchy -> Pred -> [Pred]
toHnf h p =
 if inHnf p
  then [p]
  else case reducePred h p of
         Nothing -> error $ "context reduction"
         Just ps -> toHnfs h ps

inHnf       :: Pred -> Bool
inHnf (IsIn c t) = hnf t
 where hnf (TVar v)  = True
       hnf (TCon tc) = False
       hnf (TAp t _) = hnf t
       hnf (TArrow _t1 _t2) = False 
       hnf (TTuple _args) = False 

simplify          :: ClassHierarchy -> [Pred] -> [Pred] -> [Pred]
simplify h rs []     = rs
simplify h rs (p:ps) = simplify h (p:(rs\\qs)) (ps\\qs)
 where qs       = bySuper h p
       rs \\ qs = [ r | r<-rs, r `notElem` qs ]

-----------------------------------------------------------------------------

-- defaulting ambiguous constraints


ambig :: ClassHierarchy -> [Tyvar] -> [Pred] -> [(Tyvar,[Pred],[Type])]

ambig h vs ps
  = [ (v, qs, defs h v qs) |
         v <- tv ps \\ vs,
         let qs = [ p | p<-ps, v `elem` tv p ] ]

defs     :: ClassHierarchy -> Tyvar -> [Pred] -> [Type]
defs h v qs = [ t | all ((TVar v)==) ts,
                  all (`elem` stdClasses) cs, -- XXX needs fixing
                  any (`elem` numClasses) cs, -- XXX needs fixing
                  t <- defaults, -- XXX needs fixing
                  and [ entails h [] (IsIn c t) | c <- cs ]]
 where cs = [ c | (IsIn c t) <- qs ]
       ts = [ t | (IsIn c t) <- qs ]

useDefaults     :: ClassHierarchy -> [Tyvar] -> [Pred] -> [Pred]
useDefaults h vs ps
  | any null tss = error "ambiguity"        -- XXX error message needs some work
  | otherwise    = ps \\ ps'
    where ams = ambig h vs ps
          tss = [ ts | (v,qs,ts) <- ams ]
          ps' = [ p | (v,qs,ts) <- ams, p<-qs ]

topDefaults     :: ClassHierarchy -> [Pred] -> Maybe Subst
topDefaults h ps
  | any null tss = Nothing
  | otherwise    = Just $ listToFM (zip vs (map head tss))
    where ams = ambig h [] ps
          tss = [ ts | (v,qs,ts) <- ams ]
          vs  = [ v  | (v,qs,ts) <- ams ]

defaults    :: [Type]
defaults     = map (\name -> TCon (Tycon (AQual (AModule "Prelude") (AHsIdent name)) Star))
                   ["Integer", "Double"]

stdClasses  :: [Class]
stdClasses  = (map (\name -> AQual (AModule "Prelude") (AHsIdent name))
                   ["Eq", 
                    "Ord", 
                    "Bounded", 
                    "Enum", 
                    "Ix",
                    "Show", 
                    "Read",
                    "Functor", 
                    "Monad"]
              ) ++ numClasses

numClasses  :: [Class]
numClasses   = map (\name -> AQual (AModule "Prelude") (AHsIdent name))
                   ["Num", 
                    "Real",
                    "Integral", 
                    "Fractional", 
                    "Floating",
                    "RealFrac", 
                    "RealFloat"]
