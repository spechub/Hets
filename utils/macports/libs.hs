import System.Process
import Data.Char
import Data.List
import Data.Maybe

main = getDepLibs "hets"

getDepLibs :: String -> IO ()
getDepLibs binOrLib = do
   str <- readProcess "otool" ["-L", binOrLib] ""
   let ls = map (takeWhile $ not . isSpace)
               $ catMaybes
               $ map (stripPrefix lib . dropWhile isSpace) $ lines str
   mapM_ (handleLibs binOrLib) ls

lib :: String
lib = "/opt/local/lib/"

handleLibs :: String -> String -> IO ()
handleLibs binOrLib s = do
   rawSystem "cp" $ (lib ++ s) : ["."]
   rawSystem "install_name_tool" ["-id", s, s]
   rawSystem "install_name_tool" ["-change", lib ++ s, "@executable_path/" ++ s, binOrLib]
   putStrLn s
   getDepLibs s
