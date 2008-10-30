module Paths_tabular (
	version,
	getBinDir, getLibDir, getDataDir, getLibexecDir,
	getDataFileName
	) where

import Data.Version

version :: Version
version = Version {versionBranch = [0,1], versionTags = []}

bindir, libdir, datadir, libexecdir :: FilePath

bindir     = "/home/till/.ghc/i686-Linux-hets-packages/bin"
libdir     = "/home/till/.ghc/i686-Linux-hets-packages/lib/tabular-0.1/ghc-6.8.3"
datadir    = "/home/till/.ghc/i686-Linux-hets-packages/share/tabular-0.1"
libexecdir = "/home/till/.ghc/i686-Linux-hets-packages/libexec"

getBinDir, getLibDir, getDataDir, getLibexecDir :: IO FilePath
getBinDir = return bindir
getLibDir = return libdir
getDataDir = return datadir
getLibexecDir = return libexecdir

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = return (datadir ++ "/" ++ name)
