{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 TypeSynonyms

        Description:            Remove type Synonyms from types.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module TypeSynonyms (removeSynsFromSig, 
                     removeSynsFromSigs, 
                     removeSynonymsFromType,
                     removeSynonymFromType,
                     oneTypeReplace) where

import AnnotatedHsSyn            -- everything

import Utils            (getUnQualName)

--------------------------------------------------------------------------------

removeSynsFromSigs :: [AHsDecl] -> [AHsDecl] -> [AHsDecl]
removeSynsFromSigs syns sigsBinds 
   = [removeMultSynFromSig syns syns s s | s <- sigsBinds] 

-- removes all synonyms from a signature
removeSynsFromSig :: [AHsDecl] -> AHsDecl -> AHsDecl
removeSynsFromSig syns sig
   = removeMultSynFromSig syns syns sig sig
 
removeMultSynFromSig :: [AHsDecl] -> [AHsDecl] -> AHsDecl -> AHsDecl -> AHsDecl
removeMultSynFromSig [] syns oldSig newSig
   | oldSig == newSig = newSig
   | otherwise = removeMultSynFromSig syns syns newSig newSig

removeMultSynFromSig (syn:ss) syns oldSig newSig
   = removeMultSynFromSig ss syns oldSig $ removeOneSynFromSig syn newSig

removeOneSynFromSig :: (AHsDecl) -> (AHsDecl) -> (AHsDecl)

removeOneSynFromSig synonym (AHsTypeSig sloc names (AHsQualType ctxt typ))
   = AHsTypeSig sloc names (AHsQualType ctxt (removeSynonymFromType synonym typ)) 

removeOneSynFromSig synonym (AHsTypeSig sloc names (AHsUnQualType typ))
   = AHsTypeSig sloc names (AHsUnQualType (removeSynonymFromType synonym typ))
   
removeSynonymsFromType :: [(AHsDecl)] -> AHsType -> AHsType
removeSynonymsFromType syns t
   = removeMultSynFromType syns syns t t 

removeMultSynFromType :: [AHsDecl] -> [AHsDecl] -> AHsType -> AHsType -> AHsType
removeMultSynFromType [] syns oldType newType
   | oldType == newType = newType
   | otherwise = removeMultSynFromType syns syns newType newType 
removeMultSynFromType (syn:ss) syns oldType newType 
   = removeMultSynFromType ss syns oldType $ removeSynonymFromType syn newType 

removeSynonymFromType :: AHsDecl -> AHsType -> AHsType

removeSynonymFromType decl@(AHsTypeDecl _sloc name args t1) (AHsTyFun t2 t3)
   = AHsTyFun (removeSynonymFromType decl t2) (removeSynonymFromType decl t3)

removeSynonymFromType decl@(AHsTypeDecl _sloc name args t1) (AHsTyTuple tupArgs)
   = AHsTyTuple $ map (removeSynonymFromType decl) tupArgs

removeSynonymFromType decl@(AHsTypeDecl _sloc name args t1) (AHsTyApp t2 t3)
   = let declType = synToAHsType decl
         t2Remove = removeSynonymFromType decl t2
         t3Remove = removeSynonymFromType decl t3
         matches =  typesMatch declType (AHsTyApp t2Remove t3Remove)
     in  case matches of
             Nothing -> (AHsTyApp t2Remove t3Remove)
             Just matchList -> replaceVarsWithTypes matchList t1 

removeSynonymFromType decl@(AHsTypeDecl _sloc name args t1) (AHsTyCon n)
   = let declType = synToAHsType decl
         matches = typesMatch declType (AHsTyCon n)
     in  case matches of
              Nothing -> (AHsTyCon n)
              Just matchList -> replaceVarsWithTypes matchList t1
         
removeSynonymFromType decl@(AHsTypeDecl _sloc name args t1) (AHsTyVar v)
   = AHsTyVar v

removeSynonymFromType _ _
   = error "removeSynonymFromType: applied to a decl that was not a type synomym"

synToAHsType :: AHsDecl -> AHsType
synToAHsType (AHsTypeDecl _ name args _)
   = foldl AHsTyApp (AHsTyCon name) (map (\arg -> AHsTyVar arg) args)


typesMatch :: AHsType -> AHsType -> Maybe [(AHsType, AHsType)]

typesMatch (AHsTyApp t1 t2) (AHsTyApp t3 t4) 
   = case typesMatch t1 t3 of
          Nothing -> Nothing
          Just matches1 -> case typesMatch t2 t4 of
                                Nothing -> Nothing
                                Just matches2 -> Just (matches1 ++ matches2)

typesMatch (AHsTyVar var) otherType
   = Just [(AHsTyVar var, otherType)] 

-- XXX this is broken, doesn't handle synonyms from different modules
-- with the same name ie
-- thinks Foo.String and Prelude.String and String are all the same thing
-- this needs to be fixed by renaming things properly. Until the renamer
-- is written we will have to put up with this version.
typesMatch (AHsTyCon name1) (AHsTyCon name2)
   = if name1Str == name2Str then Just [] else Nothing
   -- = error $ show name1 ++ " " ++ show name2 
   where
   name1Str = getUnQualName name1
   name2Str = getUnQualName name2

typesMatch _ _ = Nothing


replaceVarsWithTypes :: [(AHsType, AHsType)] -> AHsType -> AHsType

replaceVarsWithTypes [] typ = typ

replaceVarsWithTypes (repl:replacements) typ
   = replaceVarsWithTypes replacements (oneTypeReplace repl typ)

oneTypeReplace :: (AHsType, AHsType) -> AHsType -> AHsType

oneTypeReplace (old, new) var@(AHsTyVar name)
  | old == var = new
  | otherwise = var

oneTypeReplace (old, new) (AHsTyFun t1 t2)
   = AHsTyFun (oneTypeReplace (old, new) t1) (oneTypeReplace (old, new) t2)

oneTypeReplace (old, new) (AHsTyApp t1 t2)
   = AHsTyApp (oneTypeReplace (old, new) t1) (oneTypeReplace (old, new) t2)

oneTypeReplace (old, new) (AHsTyTuple args)
   = AHsTyTuple $ map (oneTypeReplace (old, new)) args

oneTypeReplace (old, new) (AHsTyCon n)
   = AHsTyCon n
