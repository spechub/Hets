{-------------------------------------------------------------------------------

        Copyright:              The Hatchet Team (see file Contributors)

        Module:                 Utils

        Description:            Generic utilities that don't have a good home 
                                anywhere else.

        Primary Authors:        Bernie Pope

        Notes:                  See the file License for license information

-------------------------------------------------------------------------------}

module Utils (getAModuleName,
              maybeGetDeclName,
              getDeclName,
              doDump,
              fromAHsName,
              fromAHsIdentifier,
              isBindDecl,
              isDataDecl,
              isSigDecl,
              isQualified,
              qualifyName,
              getUnQualName,
              fst3,
              snd3,
              trd3,
              showListAndSep,
              showListAndSepInWidth,
              nameSupply,
              nameOfTyCon,
              groupEquations,
              spacesToUnderscores,
              rJustify,
              lJustify,
              Binding (..)
             ) where

import AnnotatedHsSyn       -- almost everything 

import FiniteMaps       (listToFM,
                         FiniteMap)

import Char             (isUpper, 
                         isSpace)

import HsPretty        (PPHsMode (..),
                        PPLayout (..),
                        render
                       )

import Pretty          (Doc,
                        (<>),
                        text)

import PPrint          (PPrint (..))

import Monad           (when)

--------------------------------------------------------------------------------

getAModuleName :: AHsModule -> AModule
getAModuleName (AHsModule modName _exporta _imports _decls)
   = modName

maybeGetDeclName :: AHsDecl -> Maybe AHsName
maybeGetDeclName (AHsPatBind sloc (AHsPVar name) rhs wheres) = Just name
maybeGetDeclName (AHsFunBind ((AHsMatch _ name _ _ _):_)) = Just name
maybeGetDeclName (AHsDataDecl _ _ name  _ _ _) = Just name
maybeGetDeclName (AHsClassDecl _ qualType _)
   = case qualType of
        AHsQualType _cntxt t
           -> Just $ leftMostTyCon t
        AHsUnQualType t
           -> Just $ leftMostTyCon t 
maybeGetDeclName _ = Nothing

getDeclName :: AHsDecl -> AHsName
getDeclName (AHsPatBind sloc (AHsPVar name) rhs wheres) = name
getDeclName (AHsFunBind ((AHsMatch _ name _ _ _):_)) = name
getDeclName (AHsDataDecl _ _ name  _ _ _) = name
getDeclName (AHsNewTypeDecl _ _ name  _ _ _) = name
getDeclName (AHsClassDecl _ qualType _)
   = case qualType of
        AHsQualType _cntxt t
           -> leftMostTyCon t
        AHsUnQualType t
           -> leftMostTyCon t
getDeclName d = error $ "getDeclName: could not find name for a decl" 


-- gets the left most type constructor from a type

leftMostTyCon (AHsTyTuple ts) = error "leftMostTyCon: applied to a tuple"
leftMostTyCon (AHsTyApp t1 _) = leftMostTyCon t1 
leftMostTyCon (AHsTyVar _) = error "leftMostTyCon: applied to a variable"
leftMostTyCon (AHsTyCon n) = n

fromAHsName :: AHsName -> String
fromAHsName (AUnQual i) = fromAHsIdentifier i 
fromAHsName (AQual (AModule m) i) = m ++ "." ++ (fromAHsIdentifier i)

fromAHsIdentifier :: AHsIdentifier -> String
fromAHsIdentifier (AHsIdent s) = s
fromAHsIdentifier (AHsSymbol s) = s
fromAHsIdentifier (AHsSpecial s) = s

isBindDecl :: AHsDecl -> Bool
isBindDecl (AHsPatBind _ _ _ _) = True
isBindDecl (AHsFunBind _) = True 
isBindDecl _ = False

isDataDecl :: AHsDecl -> Bool
isDataDecl (AHsDataDecl _ _ _ _ _ _) = True
isDataDecl _ = False 

isSigDecl :: AHsDecl -> Bool
isSigDecl (AHsTypeSig _sloc _names _qualType) = True
isSigDecl _ = False

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a
snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b
trd3 :: (a,b,c) -> c
trd3 (_,_,c) = c

-- takes a list of things and puts a seperator string after each elem
-- except the last, first arg is a function to convert the things into
-- strings
showListAndSep :: (a -> String) -> String -> [a] -> String
showListAndSep f sep []
   = []
showListAndSep f sep [s]
   = f s
showListAndSep f sep (s:ss)
   = f s ++ sep ++ showListAndSep f sep ss

accLen :: Int -> [[a]] -> [(Int, [a])]
accLen width [] = []
accLen width (x:xs)
   = let newWidth
           = length x + width
     in (newWidth, x) : accLen newWidth xs

groupStringsToWidth :: Int -> [String] -> [String]
groupStringsToWidth width ss
   = groupStringsToWidth' width (accLen 0 ss)
   where
   groupStringsToWidth' :: Int -> [(Int,String)] -> [String]
   groupStringsToWidth' width [] = []
   groupStringsToWidth' width xs
      = headString : groupStringsToWidth' width (accLen 0 $ map snd rest)
      where
      (headSegments, rest)
         = case span ((<=width).fst) xs of
              ([], ss)     -> ([head ss], tail ss)
              anythingElse -> anythingElse
      headString = concatMap snd headSegments

showListAndSepInWidth :: (a -> String) -> Int -> String -> [a] -> String
showListAndSepInWidth _ _ _ [] = []
showListAndSepInWidth f width sep things
   = unlines $ groupStringsToWidth width newThings
   where
   newThings = (map ((\t -> t ++ sep).f) (init things)) ++ [f (last things)]

-- an infinite list of alphabetic strings in the usual order
nameSupply :: [String]
nameSupply
  = [ x++[y] | x <- []:nameSupply, y <- ['a'..'z'] ]

nameOfTyCon :: AHsType -> AHsName
nameOfTyCon (AHsTyCon n) = n
nameOfTyCon t = error $ "nameOfTyCon: " ++ show t

groupEquations :: [AHsDecl] -> [(AHsName, AHsDecl)]
groupEquations [] = []
groupEquations (d:ds)
   = (getDeclName d, d) : groupEquations ds 

spacesToUnderscores :: String -> String
spacesToUnderscores 
   = map $ \c -> if (isSpace c) then '_' else c

rJustify :: Int -> String -> String
rJustify n s = replicate (n - length s) ' ' ++ s

lJustify :: Int -> String -> String
lJustify n s = take n $ s ++ repeat ' ' 

doDump :: [String] -> String -> Bool
doDump ss s
   = s `elem` ss || "all" `elem` ss

-- True if a AHsName is qualified
isQualified :: AHsName -> Bool
isQualified (AQual _ _) = True
isQualified (AUnQual _) = False

-- returns the string component of a name, in unqualified form

getUnQualName :: AHsName -> String
getUnQualName (AQual _ n) = fromAHsIdentifier n
getUnQualName (AUnQual n) = fromAHsIdentifier n

-- module qualifies a name if it isn't already qualified

qualifyName :: AModule -> AHsName -> AHsName
qualifyName _mod name@(AQual _ _) = name
qualifyName mod (AUnQual name) = AQual mod name

-- -- The possible bindings for names 

data Binding
   = TopFun             -- function binding at the top level
   | ClassMethod        -- name of a method in a class
   | Instance           -- an instance decl lifted to a top-level binding
   | WhereFun           -- function binding in a where clause
   | LetFun             -- function binding in a let expression (used to include topbinds too)
   | LamPat             -- pattern binding in a lambda expression
   | CasePat            -- pattern binding in a case expression
   | GenPat             -- pattern binding in a generator statement
   | FunPat             -- pattern binding in a function declaration
   | Constr             -- name is a data constructor 
   deriving (Show, Eq, Enum)

-- pretty printing a AHsName, AModule and AHsIdentifier

instance PPrint AHsName where
   pprint (AQual mod ident)
      -- don't print the Prelude module qualifier
      | mod == AModule "Prelude" = pprint ident
      | otherwise                = pprint mod <> text "." <> pprint ident
   pprint (AUnQual ident)
      = pprint ident

instance PPrint AModule where
   pprint (AModule s) = text s

instance PPrint AHsIdentifier where
   pprint (AHsIdent   s) = text s 
   pprint (AHsSymbol  s) = text s 
   pprint (AHsSpecial s) = text s 
