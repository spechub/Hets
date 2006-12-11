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
try x = catch (x >>= return . Right) (return . Left)

-- Parser - extract data and newtypes from code  

type ToDo = [([Tag],Data)]

parser :: String -> ToDo
parser = sanitycheck . papply p (0,0) . \s -> ((0,0),s)
        where    
       p = parse . skipUntilOff $ statement +++ command
       statement = do d <- datadecl +++ newtypedecl
                      ts <- opt local
                      return (ts,d)
       sanitycheck [] = error "***Error: no DrIFT directives found\n"
       sanitycheck [(x,_)] = x
       sanitycheck ((x,_):_) = error "***Error: ambiguous DriFT directives?"

-------Go Hunting for files, recursively ----------------------------------

chaseImports :: String -> ToDo -> IO ToDo
chaseImports txt dats = do
        (left,found) <- chaseImports' txt dats
        if (not . null) left then error ("can't find type " ++ show left)
         else return found

chaseImports' :: String -> ToDo ->  IO (ToDo,ToDo)
chaseImports' text dats = 
  case papply (parse header) (0,-1) ((0,0),text) of
        [] -> return (dats,[])
        (modnames:_) -> foldM action (dats,[]) (fst modnames)
    where
        action :: (ToDo,ToDo) -> FilePath -> IO (ToDo,ToDo)     
        action (dats,done) m | null dats = return ([],done)
                             | otherwise = do 
             mp <- ioM $ getEnv "DERIVEPATH"
             let paths = maybe [] breakPaths mp 
             c <- findModule paths m
             let (found,rest) = scanModule m dats c
             return (rest, done ++ found) -- finished
             -- only one level of imports is now supported for more speed!
                        
-- break DERIVEPATH into it's components                        
breakPaths :: String -> [String]
breakPaths x = case break (==':') x of
        (p,(_:pp)) -> p: breakPaths pp
        (p,[]) -> [p]

-- search though paths, using try
findModule :: [String] -> String -> IO String
findModule paths modname = let
        action p = try $ do 
                            h <- readFile p 
                            return (h,p)
        fnames = combine paths hiracle_modname
        hiracle_modname = map (\x -> if x == '.' then '/' else x) modname
        isLeft (Left _ ) = True
        isLeft _ = False
     in do
        hh <- mapM action fnames
        let (h,p) = case dropWhile (isLeft) hh of
                   ((Right h):_) -> h
                   _ -> error ("can't find module " ++ modname)
        return h

-- generate filepaths by combining module names with different suffixes.
-- Note : Dedicated Hugs-only users may wish to remove ".hi" from the list of
-- file types to search.  
combine :: [String] -> String -> [FilePath]     
combine paths modname = [p++'/':f| f <- toFile modname, p <- ("." :paths)]
        where
             toFile :: String -> [String]
             toFile l = [l++".hs",l++".lhs",l++".hi"] 

-- pluck out the bits of interest
scanModule :: String -> ToDo -> String -> (ToDo,ToDo)
scanModule modname dats txt = let 
        newDats = filter isData . parse $ txt
        parse l = map snd . parser $ l
        in (resolve modname newDats dats ([],[]))

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


