-- ------------------------------------------------------------
--
-- GET for local file access
--
-- Version : $Id$

module Text.XML.HXT.IO.GetFILE
    ( module Text.XML.HXT.IO.GetFILE
    )

where

import System.IO
    ( IOMode(..)
    , openFile
    , hGetContents
    )

import System.IO.Error
    ( ioeGetErrorString
    , try
    )

import System.Directory
    ( doesFileExist
    , getPermissions
    , readable
    )

-- ------------------------------------------------------------

getCont		:: String -> IO (Either String String)
getCont source
    = do			-- preliminary
      exists <- doesFileExist source
      if not exists
	 then return (Left ("file " ++ show source ++ " not found"))
	 else do
	      perm <- getPermissions source
	      if not (readable perm)
	         then return (Left ("file " ++ show source ++ " not readable"))
	         else do
		      c <- try ( do
				 h <- openFile source ReadMode
				 hGetContents h
			       )
		      return (either readErr Right c)
    where
    readErr e
	= Left ( "system error when reading file "
		 ++ show source
		 ++ ": "
		 ++ ioeGetErrorString e
	       )

-- ------------------------------------------------------------
