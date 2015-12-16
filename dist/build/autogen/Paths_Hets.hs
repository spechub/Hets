module Paths_Hets (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,99] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/marie/.cabal/bin"
libdir     = "/home/marie/.cabal/lib/i386-linux-ghc-7.8.4/Hets-0.99"
datadir    = "/home/marie/.cabal/share/i386-linux-ghc-7.8.4/Hets-0.99"
libexecdir = "/home/marie/.cabal/libexec"
sysconfdir = "/home/marie/.cabal/etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "Hets_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "Hets_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "Hets_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "Hets_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "Hets_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
