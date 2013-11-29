import System.Process
import Data.Char
import Data.List
import Data.Maybe

main = getDepLibs "hets"

getDepLibs :: String -> IO ()
getDepLibs binOrLib = do
   str <- readProcess "otool" ["-L", binOrLib] ""
   let ls = map (takeWhile $ not . isSpace)
               $ mapMaybe (stripPrefix lib . dropWhile isSpace) $ lines str
   mapM_ (handleLibs binOrLib) ls

lib :: String
lib = "/opt/local/lib/"

handleLibs :: String -> String -> IO ()
handleLibs binOrLib s = do
   rawSystem "cp" $ (lib ++ s) : ["."]
   let name = "@executable_path/" ++ s
   rawSystem "install_name_tool" ["-id", name, s]
   rawSystem "install_name_tool" ["-change", lib ++ s, name, binOrLib]
   putStrLn s
   getDepLibs s
