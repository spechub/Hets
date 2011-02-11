{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  A Haskell MathLink interface
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  experimental
Portability :  non-portable (see language extensions)

A Haskell MathLink interface based on the Foreign.MathLink.Bindings module
-}


module Common.MathLink where

import Foreign.C -- get the C types
import Foreign.Marshal -- get the array marshalling utils
import Foreign.Storable
import Foreign.Ptr (Ptr,nullPtr)

import Foreign.MathLink.Bindings
 
import Control.Monad.Reader
import System.Timeout
import System.IO


-- * Constants for the MathLink interface

dfMLTKAEND, dfMLTKALL_DECODERS, dfMLTKAPCTEND, dfMLTKARRAY, dfMLTKARRAY_DECODER
 , dfMLTKCONT, dfMLTKDIM, dfMLTKELEN, dfMLTKEND, dfMLTKERR, dfMLTKERROR
 , dfMLTKFUNC, dfMLTKINT, dfMLTKMODERNCHARS_DECODER, dfMLTKNULL
 , dfMLTKNULLSEQUENCE_DECODER, dfMLTKOLDINT, dfMLTKOLDREAL, dfMLTKOLDSTR
 , dfMLTKOLDSYM, dfMLTKPACKED_DECODER, dfMLTKPACKED, dfMLTKPCTEND, dfMLTKREAL
 , dfMLTKSEND, dfMLTKSTR, dfMLTKSYM, dfRETURNPKT, dfRETURNTEXTPKT
 , dfRETURNEXPRPKT :: CInt

dfRETURNPKT = 3
dfRETURNTEXTPKT = 4
dfRETURNEXPRPKT = 16


dfMLTKAEND=13
dfMLTKALL_DECODERS=983040
dfMLTKAPCTEND=10
dfMLTKARRAY=65
dfMLTKARRAY_DECODER=262144
dfMLTKCONT=92
dfMLTKDIM=68
dfMLTKELEN=32
dfMLTKEND=10
dfMLTKERR=0
dfMLTKERROR=0
dfMLTKFUNC=70
dfMLTKINT=43
dfMLTKMODERNCHARS_DECODER=524288
dfMLTKNULL=46
dfMLTKNULLSEQUENCE_DECODER=0
dfMLTKOLDINT=73
dfMLTKOLDREAL=82
dfMLTKOLDSTR=83
dfMLTKOLDSYM=89
dfMLTKPACKED_DECODER=131072
dfMLTKPACKED=80
dfMLTKPCTEND=93
dfMLTKREAL=42
dfMLTKSEND=44
dfMLTKSTR=34
dfMLTKSYM=35


-- * MathLink monad as Reader IO monad

data MLState =
    MLState
    { mlink :: MLINK
    , logHdl :: Maybe Handle
    }

mkState :: MLINK -> MLState
mkState mlp = MLState { mlink = mlp, logHdl = Nothing }

mkStateWithLog :: MLINK -> Handle -> MLState
mkStateWithLog mlp hdl = MLState { mlink = mlp, logHdl = Just hdl }

type ML = ReaderT MLState IO

askMLink :: ML MLINK
askMLink = asks mlink

logMessage :: String -> ML ()
logMessage s = do
  mHdl <- asks logHdl
  case mHdl of
    Just hdl -> liftIO $ hPutStr hdl s
    Nothing -> liftIO $ putStr s

logMessageLn :: String -> ML ()
logMessageLn s = do
  mHdl <- asks logHdl
  case mHdl of
    Just hdl -> liftIO $ hPutStrLn hdl s
    Nothing -> liftIO $ putStrLn s

liftMLIO :: (MLINK -> IO b) -> ML b
liftMLIO f = askMLink >>= liftIO . f


-- * MathLink connection handling

connectLink :: MLINK -> IO Bool
connectLink lp = do
  let p i j = do
        i' <- cMlReady lp
        if toBool i' || j > 3000 then return j
         else cMlFlush lp >> if i > 1000 then p 0 (j+1) else p (i+1) j

  p (0::Int) (0::Int) >>= putStrLn . ("ready after " ++) . show

  res <- cMlConnect lp
  return $ toBool res

runLink :: Maybe FilePath -> Maybe String -> ML a -> IO (Either Int a)
runLink mFP mName mlprog = do
--  env <- mlInitialize ""
  env <- cMlInitialize nullPtr
  if (env == nullPtr) then return $ Left 1
   else do
    putStrLn "Initialized"

    let (name, mode) = case mName of
                         Just n -> (n, "connect")
                         _ -> ("math -mathlink", "launch")

    let openargs = ["-linkname", name, "-linkmode", mode]

    lp <- mlOpen 4 openargs
    mB <- if lp == nullPtr then return Nothing
--          else liftM Just $ connectLink lp
          else timeout 3000000 $ connectLink lp
    
    case mB of
      Nothing -> return $ Left 2
      Just False -> return $ Left 3
      _ ->
          do
            putStrLn "Opened"
            x <- case mFP of
                   Just fp ->
                       withFile fp WriteMode $ runReaderT mlprog . mkStateWithLog lp
                   Nothing ->
                       runReaderT mlprog $ mkState lp
            mlClose lp
            mlDeinitialize env
            return $ Right x
  

mlInitialize  :: String -> IO MLEnvironment
mlInitialize = flip withCString cMlInitialize

mlDeinitialize  :: MLEnvironment -> IO ()
mlDeinitialize = cMlDeinitialize

mlOpen  :: CInt -> [String] -> IO MLINK
mlOpen i l = withStringArray l $ cMlOpen i



-- * C to Haskell utilities

withStringArray :: MonadIO m => [String] -> (Ptr CString -> IO b) -> m b
withStringArray l f = liftIO $ mapM newCString l >>= flip withArray f


mlGetA  :: (Storable a, Show a, Show b) => (Ptr a -> IO b) -> IO a
mlGetA f = let g ptr = f ptr >> peek ptr in alloca g


-- maybe better via foreign pointer, check later
mlGetCString  :: Show b => (Ptr CString -> IO b) -> (CString -> IO ()) -> IO String
mlGetCString f disownF =
    let g ptr = do
          cs <- f ptr >> peek ptr
          s <- peekCString cs
          disownF cs
          return s
    in alloca g


-- * Haskell friendly MathLink interface built on top of the raw bindings

mlClose  :: MLINK -> IO CInt
mlClose = cMlClose

mlFlush  :: ML CInt
mlFlush = liftMLIO cMlFlush

mlReady  :: ML CInt
mlReady = liftMLIO cMlReady

mlConnect  :: ML CInt
mlConnect = liftMLIO cMlConnect

mlEndPacket  :: ML CInt
mlEndPacket = liftMLIO cMlEndPacket

mlNextPacket  :: ML CInt
mlNextPacket = liftMLIO cMlNextPacket

mlNewPacket  :: ML CInt
mlNewPacket = liftMLIO cMlNewPacket

mlGetNext  :: ML CInt
mlGetNext = liftMLIO cMlGetNext


mlGetArgCount :: ML CInt
mlGetArgCount = askMLink >>= liftIO . mlGetA . cMlGetArgCount

mlGetArgCount' :: ML Int
mlGetArgCount' = liftM cintToInt mlGetArgCount



cintToInteger :: CInt -> Integer
cintToInteger = fromIntegral

intToCInt :: Int -> CInt
intToCInt = fromIntegral

-- These two functions are unsafe, they may overflow...
integerToCInt :: Integer -> CInt
integerToCInt = fromIntegral

cintToInt :: CInt -> Int
cintToInt = fromIntegral



cdblToDbl :: CDouble -> Double
cdblToDbl = realToFrac

dblToCDbl :: Double -> CDouble
dblToCDbl = realToFrac




-- cMlGetSymbol  :: MLINK -> Ptr CString -> IO CInt
mlGetSymbol  :: ML String
mlGetSymbol = do
  ml <- askMLink
  liftIO $ mlGetCString (cMlGetSymbol ml) $ cMlDisownSymbol ml

-- cMlGetString  :: MLINK -> Ptr CString -> IO CInt
mlGetString  :: ML String
--mlGetString = askMLink >>= liftIO . mlGetCString . cMlGetString
mlGetString = do
  ml <- askMLink
  liftIO $ mlGetCString (cMlGetString ml) $ cMlDisownString ml

-- cMlGetReal  :: MLINK -> Ptr CDouble -> IO CInt
mlGetReal  :: ML CDouble
mlGetReal = askMLink >>= liftIO . mlGetA . cMlGetReal

mlGetReal'  :: ML Double
mlGetReal' = liftM cdblToDbl mlGetReal

-- cMlGetInteger  :: MLINK -> Ptr CInt -> IO CInt
mlGetInteger  :: ML CInt
mlGetInteger = askMLink >>= liftIO . mlGetA . cMlGetInteger

mlGetInteger'  :: ML Integer
mlGetInteger' = liftM cintToInteger mlGetInteger

mlPutString  :: String -> ML CInt
mlPutString s = liftMLIO f where
    f ml = withCString s $ cMlPutString ml

mlPutSymbol  :: String -> ML CInt
mlPutSymbol s = liftMLIO f where
    f ml = withCString s $ cMlPutSymbol ml

mlPutFunction  :: String -> CInt -> ML CInt
mlPutFunction s i = liftMLIO f where
    f ml = withCString s $ flip (cMlPutFunction ml) i

mlPutFunction'  :: String -> Int -> ML CInt
mlPutFunction' s = mlPutFunction s . intToCInt

mlPutInteger  :: CInt -> ML CInt
mlPutInteger = liftMLIO . flip cMlPutInteger

mlPutInteger'  :: Integer -> ML CInt
mlPutInteger' = mlPutInteger . integerToCInt

mlPutReal  :: CDouble -> ML CInt
mlPutReal = liftMLIO . flip cMlPutReal
 
mlPutReal'  :: Double -> ML CInt
mlPutReal' = mlPutReal . dblToCDbl


mlError  :: ML CInt
mlError = liftMLIO cMlError

mlErrorMessage  :: ML String
mlErrorMessage = liftMLIO (cMlErrorMessage >=> peekCString)


-- * MathLink interface utils

mlProcError :: ML ()
mlProcError = do
  eid <- mlError
  if toBool eid then mlErrorMessage >>= logMessageLn . ("Error detected by MathLink: " ++)
   else logMessageLn "Error detected by Interface"

receivePacket :: ML ()
receivePacket = do
  -- skip any packets before the first ReturnPacket
  waitUntilPacket (0::Int) [dfRETURNPKT, dfRETURNEXPRPKT, dfRETURNTEXTPKT]

waitUntilPacket :: Num a => a -> [CInt] -> ML ()
waitUntilPacket i l = do
  np <- mlNextPacket
  if elem np l then logMessageLn $ "GotReturn after " ++ show i ++ " iterations"
   else (logMessageLn $ "wap: " ++ show np) >> mlNewPacket >> waitUntilPacket (i+1) l

