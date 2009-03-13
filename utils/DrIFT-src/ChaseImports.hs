{- this module coordinates the whole shebang.
  Parses input and plucks out data and newtype declarations and
  processor commands.
  The commands are combined with the parsed data, and if any data is missing,
  derive goes hunting for it, looking in
  the path variable DERIVEPATH. Derive searches recusively though modules
  imported until all the types needed are found, or it runs out of links,
  which causes an error -}

module ChaseImports where

import RuleUtils (Tag)
import DataP
import CommandP
import ParseLib2
import System
import List
import Monad
import GenUtil

--GHC version
try :: IO a -> IO (Either IOError a)
try x = catch (x >>= return . Right) (return . Left)

-- Parser - extract data and newtypes from code

type ToDo = [([Tag], Data)]

parser :: String -> ToDo
parser = sanitycheck . papply p (0, 0) . \ s -> ((0, 0), s)
        where
       p = parse . skipUntilOff $ statemnt +++ command
       statemnt = do
         d <- datadecl +++ newtypedecl
         ts <- opt local
         return (ts, d)
       sanitycheck l = case l of
         [(x, _)] -> x
         _ -> error "***Error: no or ambiguous DriFT directives"

-------Go Hunting for files, recursively ----------------------------------

chaseImports :: String -> ToDo -> IO ToDo
chaseImports txt dats = do
        (left,found) <- chaseImports' txt dats
        if (not . null) left then error ("can't find type " ++ show left)
         else return found

chaseImports' :: String -> ToDo ->  IO (ToDo, ToDo)
chaseImports' text indats =
  case papply (parse header) (0, -1) ((0, 0), text) of
        [] -> return (indats, [])
        (modnames:_) -> foldM action (indats, []) (fst modnames)
    where
        action :: (ToDo, ToDo) -> FilePath -> IO (ToDo, ToDo)
        action (dats, done) m = if null dats then return ([], done) else do
             mp <- ioM $ getEnv "DERIVEPATH"
             let paths = maybe [] breakPaths mp
             mc <- findModule paths m
             return $ case mc of
               Nothing -> (dats, done)
               Just c -> let (found, rest) = scanModule m dats c in
                 (rest, done ++ found)
             -- only one level of imports is now supported for more speed!

-- break DERIVEPATH into it's components
breakPaths :: String -> [String]
breakPaths x = case break (flip elem ":;") x of
        (p, _ : pp) -> p : breakPaths pp
        (p, []) -> [p]

-- search through paths, using try
findModule :: [String] -> String -> IO (Maybe String)
findModule paths modname = do
    let action p = try $ readFile p
        fnames = combine paths hiracle_modname
        hiracle_modname = map (\ x -> if x == '.' then '/' else x) modname
        isLeft (Left _ ) = True
        isLeft _ = False
    hh <- mapM action fnames
    case dropWhile (isLeft) hh of
              Right h : _ -> return $ Just h
              _ -> return Nothing

-- generate filepaths by combining module names with different suffixes.
-- Note : Dedicated Hugs-only users may wish to remove ".hi" from the list of
-- file types to search.
combine :: [String] -> String -> [FilePath]
combine paths modname = [p ++ '/' : modname ++ ".hs" | p <- "." : paths]

-- pluck out the bits of interest
scanModule :: String -> ToDo -> String -> (ToDo, ToDo)
scanModule modname dats txt = let
        newDats = filter isData . myparse $ txt
        myparse l = map snd . parser $ l
        in resolve modname newDats dats ([], [])

-- update what's still missing
resolve :: String -> [Data] -> ToDo -> (ToDo,ToDo) -> (ToDo,ToDo)
resolve _ _ [] acc = acc
resolve modname parsed (tv:tt) p@(local, imports) =
    case tv of
    (tags, TypeName t) ->
        case filter ( \ d -> name d == t ||
                             modname ++ "." ++ name d == t) parsed of
          [x] -> resolve modname parsed tt
                 ( (tags, x { name = modname ++ "." ++ name x }) : local
                 , imports)
          _ -> resolve modname parsed tt (local, tv : imports)
    _ -> resolve modname parsed tt p

-- utils -- this should be the sort of thing automatically generated !!
isData D{} = True
isData _ = False


