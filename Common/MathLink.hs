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

import Data.Maybe

import Common.Utils


-- * Constants for the MathLink interface

dfMLTKAEND, dfMLTKALL_DECODERS, dfMLTKAPCTEND, dfMLTKARRAY,
 dfMLTKARRAY_DECODER , dfMLTKCONT, dfMLTKDIM, dfMLTKELEN, dfMLTKEND,
 dfMLTKERR, dfMLTKERROR , dfMLTKFUNC, dfMLTKINT,
 dfMLTKMODERNCHARS_DECODER, dfMLTKNULL , dfMLTKNULLSEQUENCE_DECODER,
 dfMLTKOLDINT, dfMLTKOLDREAL, dfMLTKOLDSTR , dfMLTKOLDSYM,
 dfMLTKPACKED_DECODER, dfMLTKPACKED, dfMLTKPCTEND, dfMLTKREAL ,
 dfMLTKSEND, dfMLTKSTR, dfMLTKSYM, dfILLEGALPKT, dfCALLPKT,
 dfEVALUATEPKT , dfRETURNPKT, dfINPUTNAMEPKT, dfENTERTEXTPKT,
 dfENTEREXPRPKT, dfOUTPUTNAMEPKT, dfRETURNTEXTPKT, dfRETURNEXPRPKT,
 dfDISPLAYPKT, dfDISPLAYENDPKT, dfMESSAGEPKT, dfTEXTPKT, dfINPUTPKT,
 dfINPUTSTRPKT, dfMENUPKT, dfSYNTAXPKT, dfSUSPENDPKT, dfRESUMEPKT,
 dfBEGINDLGPKT, dfENDDLGPKT, dfFIRSTUSERPKT, dfLASTUSERPKT :: CInt

dfILLEGALPKT = 0

dfCALLPKT = 7
dfEVALUATEPKT = 13
dfRETURNPKT = 3

dfINPUTNAMEPKT = 8
dfENTERTEXTPKT = 14
dfENTEREXPRPKT = 15
dfOUTPUTNAMEPKT = 9
dfRETURNTEXTPKT = 4
dfRETURNEXPRPKT = 16

dfDISPLAYPKT = 11
dfDISPLAYENDPKT = 12

dfMESSAGEPKT = 5
dfTEXTPKT = 2

dfINPUTPKT = 1
dfINPUTSTRPKT = 21
dfMENUPKT = 6
dfSYNTAXPKT = 10

dfSUSPENDPKT = 17
dfRESUMEPKT = 18

dfBEGINDLGPKT = 19
dfENDDLGPKT = 20

dfFIRSTUSERPKT = 128
dfLASTUSERPKT = 255




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


showPKT :: CInt -> String
showPKT i | i == dfILLEGALPKT = "ILLEGALPKT"
          | i == dfCALLPKT = "CALLPKT"
          | i == dfEVALUATEPKT = "EVALUATEPKT"
          | i == dfRETURNPKT = "RETURNPKT"
          | i == dfINPUTNAMEPKT = "INPUTNAMEPKT"
          | i == dfENTERTEXTPKT = "ENTERTEXTPKT"
          | i == dfENTEREXPRPKT = "ENTEREXPRPKT"
          | i == dfOUTPUTNAMEPKT = "OUTPUTNAMEPKT"
          | i == dfRETURNTEXTPKT = "RETURNTEXTPKT"
          | i == dfRETURNEXPRPKT = "RETURNEXPRPKT"
          | i == dfDISPLAYPKT = "DISPLAYPKT"
          | i == dfDISPLAYENDPKT = "DISPLAYENDPKT"
          | i == dfMESSAGEPKT = "MESSAGEPKT"
          | i == dfTEXTPKT = "TEXTPKT"
          | i == dfINPUTPKT = "INPUTPKT"
          | i == dfINPUTSTRPKT = "INPUTSTRPKT"
          | i == dfMENUPKT = "MENUPKT"
          | i == dfSYNTAXPKT = "SYNTAXPKT"
          | i == dfSUSPENDPKT = "SUSPENDPKT"
          | i == dfRESUMEPKT = "RESUMEPKT"
          | i == dfBEGINDLGPKT = "BEGINDLGPKT"
          | i == dfENDDLGPKT = "ENDDLGPKT"
          | i == dfFIRSTUSERPKT = "FIRSTUSERPKT"
          | i == dfLASTUSERPKT = "LASTUSERPKT"
          | otherwise = "UNRECOGNIZED PACKET"


showTK :: CInt -> String
showTK i  | i == dfMLTKAEND = "MLTKAEND"
          | i == dfMLTKALL_DECODERS = "MLTKALL_DECODERS"
          | i == dfMLTKAPCTEND = "MLTKAPCTEND"
          | i == dfMLTKARRAY = "MLTKARRAY"
          | i == dfMLTKARRAY_DECODER = "MLTKARRAY_DECODER"
          | i == dfMLTKCONT = "MLTKCONT"
          | i == dfMLTKDIM = "MLTKDIM"
          | i == dfMLTKELEN = "MLTKELEN"
          | i == dfMLTKEND = "MLTKEND"
          | i == dfMLTKERR = "MLTKERR"
          | i == dfMLTKERROR = "MLTKERROR"
          | i == dfMLTKFUNC = "MLTKFUNC"
          | i == dfMLTKINT = "MLTKINT"
          | i == dfMLTKMODERNCHARS_DECODER = "MLTKMODERNCHARS_DECODER"
          | i == dfMLTKNULL = "MLTKNULL"
          | i == dfMLTKNULLSEQUENCE_DECODER = "MLTKNULLSEQUENCE_DECODER"
          | i == dfMLTKOLDINT = "MLTKOLDINT"
          | i == dfMLTKOLDREAL = "MLTKOLDREAL"
          | i == dfMLTKOLDSTR = "MLTKOLDSTR"
          | i == dfMLTKOLDSYM = "MLTKOLDSYM"
          | i == dfMLTKPACKED_DECODER = "MLTKPACKED_DECODER"
          | i == dfMLTKPACKED = "MLTKPACKED"
          | i == dfMLTKPCTEND = "MLTKPCTEND"
          | i == dfMLTKREAL = "MLTKREAL"
          | i == dfMLTKSEND = "MLTKSEND"
          | i == dfMLTKSTR = "MLTKSTR"
          | i == dfMLTKSYM = "MLTKSYM"


-- * MathLink monad as Reader IO monad

data MLState =
    MLState
    { mlink :: MLINK
    , menv :: MLEnvironment
    , mverbosity :: Int
    , logHdl :: Maybe Handle
    }

type ML = ReaderT MLState IO


-- | 'verbMsg' with stdout as handle
verbMsgML :: Int -> String -> ML ()
verbMsgML lvl msg = do
  hdl <- getHandle
  v <- asks mverbosity
  liftIO $ verbMsg hdl v lvl msg

-- | 'verbMsgLn' with stdout as handle
verbMsgMLLn :: Int -> String -> ML ()
verbMsgMLLn lvl msg = do
  hdl <- getHandle
  v <- asks mverbosity
  liftIO $ verbMsg hdl v lvl msg

getHandle :: ML Handle
getHandle = liftM (fromMaybe stdout) $ asks logHdl

mkState :: MLINK -> MLEnvironment -> Int -> MLState
mkState mlp env v = MLState { mlink = mlp, menv = env, mverbosity = v
                            , logHdl = Nothing }

addLogging :: MLState -> Handle -> MLState
addLogging st hdl = st { logHdl = Just hdl }

askMLink :: ML MLINK
askMLink = asks mlink

liftMLIO :: (MLINK -> IO b) -> ML b
liftMLIO f = askMLink >>= liftIO . f


-- * MathLink connection handling

-- | Open connection to MathLink or return error code on failure
openLink :: Int -- ^ Verbosity
         -> Maybe String -- ^ Connection name
                         -- (launches a new kernel if not specified)
         -> IO (Either Int MLState)
openLink v mName = do
  env <- cMlInitialize nullPtr
  if (env == nullPtr) then return $ Left 1
   else do
    verbMsgIOLn v 2 "Initialized"

    let (name, mode) = case mName of
                         Just n -> (n, "connect")
                         _ -> ("math -mathlink", "launch")

    let openargs = ["-linkname", name, "-linkmode", mode]

    lp <- mlOpen 4 openargs
    mB <- if lp == nullPtr then return Nothing
--          else liftM Just $ connectLink lp
          else timeout 3000000 $ connectLink lp v
    
    case mB of
      Nothing -> return $ Left 2
      Just False -> return $ Left 3
      _ -> return $ Right $ mkState lp env v

-- | Close connection to MathLink
closeLink :: MLState -> IO ()
closeLink st = do
  mlClose $ mlink st
  cMlDeinitialize $ menv st


-- | Run ML-program on an opened connection to MathLink
withLink :: MLState -- ^ MathLink connection
         -> Maybe FilePath -- ^ Log low level messages into this file (or STDOUT)
         -> ML a -- ^ The program to run
         -> IO a
withLink st mFp mlprog =
    case mFp of
      Just fp ->
          withFile fp WriteMode $ runReaderT mlprog . addLogging st
      Nothing ->
          runReaderT mlprog st

-- | Run ML-program on a new connection to MathLink which is closed right
-- after the execution and return the prgram result or error code on failure
runLink :: Maybe FilePath -- ^ Log low level messages into this file (or STDOUT)
        -> Int -- ^ Verbosity
        -> Maybe String -- ^ Connection name
                        -- (launches a new kernel if not specified)
        -> ML a -- ^ The program to run
        -> IO (Either Int a)
runLink mFp v mName mlprog = do
  eSt <- openLink v mName
  case eSt of
    Left i -> return $ Left i
    Right st ->
        do
          verbMsgIOLn v 2 "Opened"
          x <- withLink st mFp mlprog
          closeLink st
          return $ Right x

-- | Low level: open connection
mlOpen  :: CInt -> [String] -> IO MLINK
mlOpen i l = withStringArray l $ cMlOpen i

-- | Low level: check connection
connectLink :: MLINK
            -> Int -- ^ Verbosity
            -> IO Bool
connectLink lp v = do
  let p i j = do
        i' <- cMlReady lp
        if toBool i' || j > 3000 then return j
         else cMlFlush lp >> if i > 1000 then p 0 (j+1) else p (i+1) j

  p (0::Int) (0::Int) >>= verbMsgIOLn v 2 . ("ready after " ++) . show

  res <- cMlConnect lp
  return $ toBool res

-- | Low level: close connection
mlClose  :: MLINK -> IO CInt
mlClose = cMlClose


-- * C to Haskell utilities

withStringArray :: MonadIO m => [String] -> (Ptr CString -> IO b) -> m b
withStringArray l f = liftIO $ mapM newCString l >>= flip withArray f


mlGetA  :: (Storable a, Show a, Show b) => (Ptr a -> IO b) -> IO a
mlGetA f = let g ptr = f ptr >> peek ptr in alloca g


-- TODO: maybe better via foreign pointer, check later
mlGetCString  :: Show b => (Ptr CString -> IO b) -> (CString -> IO ()) -> IO String
mlGetCString f disownF =
    let g ptr = do
          cs <- f ptr >> peek ptr
          s <- peekCString cs
          disownF cs
          return s
    in alloca g


-- * C Type conversions

cintToInteger :: CInt -> Integer
cintToInteger = fromIntegral

intToCInt :: Int -> CInt
intToCInt = fromIntegral

-- | This function is unsafe, it may overflow...
cintToInt :: CInt -> Int
cintToInt = fromIntegral



cdblToDbl :: CDouble -> Double
cdblToDbl = realToFrac

dblToCDbl :: Double -> CDouble
dblToCDbl = realToFrac

-- * Haskell friendly MathLink interface built on top of the raw bindings

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

mlGetInteger'  :: ML Int
mlGetInteger' = liftM cintToInt mlGetInteger

-- | Integers are received as strings, because the interface supports only
-- machine integers with fixed length not arbitrary sized integers.
mlGetInteger''  :: ML Integer
mlGetInteger'' = liftM read mlGetString

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

mlPutInteger'  :: Int -> ML CInt
mlPutInteger' = mlPutInteger . intToCInt

-- | Integers are sent as strings, because the interface supports only
-- machine integers with fixed length not arbitrary sized integers.
mlPutInteger''  :: Integer -> ML CInt
mlPutInteger'' i = mlPutFunction' "ToExpression" 1 >> mlPutString (show i)
       

mlPutReal  :: CDouble -> ML CInt
mlPutReal = liftMLIO . flip cMlPutReal
 
mlPutReal'  :: Double -> ML CInt
mlPutReal' = mlPutReal . dblToCDbl


mlError  :: ML CInt
mlError = liftMLIO cMlError

mlErrorMessage  :: ML String
mlErrorMessage = liftMLIO (cMlErrorMessage >=> peekCString)


-- * MathLink interface utils

mlProcError :: ML a
mlProcError = do
  eid <- mlError
  s <- if toBool eid then liftM ("Error detected by MathLink: " ++)
       mlErrorMessage
       else return "Error detected by Interface"
  verbMsgMLLn 1 s
  error $ "mlProcError: " ++ s


sendEvalPacket :: ML a -> ML a
sendEvalPacket ml = do
  mlPutFunction "EvaluatePacket" 1
  res <- ml
  mlEndPacket
  return res

sendTextPacket :: String -> ML ()
sendTextPacket s = do
  mlPutFunction "EvaluatePacket" 1
  mlPutFunction "ToExpression" 1
  mlPutString s
  mlEndPacket
  return ()

sendTextResultPacket :: String -> ML ()
sendTextResultPacket s = do
  mlPutFunction "EvaluatePacket" 1
  mlPutFunction "ToString" 1
  mlPutFunction "ToExpression" 1
  mlPutString s
  mlEndPacket
  return ()

-- these variants does not work as expected
sendTextPacket' :: String -> ML ()
sendTextPacket' s = do
  mlPutFunction "EnterTextPacket" 1
  mlPutString s
  mlEndPacket
  return ()
sendTextPacket'' :: String -> ML ()
sendTextPacket'' s = do
  mlPutFunction "EnterExpressionPacket" 1
  mlPutFunction "ToExpression" 1
  mlPutString s
  mlEndPacket
  return ()
sendTextPacket3 :: String -> ML ()
sendTextPacket3 s = do
  mlPutFunction "EvaluatePacket" 1
  mlPutFunction "ToString" 1
  mlPutFunction "ToExpression" 1
  mlPutString s
  mlEndPacket
  return ()
sendTextPacket4 :: String -> ML ()
sendTextPacket4 s = do
  mlPutFunction "EnterExpressionPacket" 1
  mlPutFunction "ToString" 1
  mlPutFunction "ToExpression" 1
  mlPutString s
  mlEndPacket
  return ()


waitForAnswer :: ML CInt
waitForAnswer = do
    -- skip any packets before the first ReturnPacket
  i <- waitUntilPacket (0::Int) [ dfRETURNPKT, dfRETURNEXPRPKT
                                , dfRETURNTEXTPKT, dfILLEGALPKT]
  if elem i [dfILLEGALPKT, dfRETURNEXPRPKT, dfRETURNTEXTPKT]
   then error $ "waitForAnswer: encountered a " ++ showPKT i
   else return i
  

-- wait for the answer and skip it
skipAnswer :: ML CInt
skipAnswer = waitForAnswer >> mlNewPacket

waitUntilPacket :: Num a => a -> [CInt] -> ML CInt
waitUntilPacket i l = do
  np <- mlNextPacket
  if elem np l then do
                 verbMsgMLLn 2 $ "GotReturn after " ++ show i ++ " iterations"
                 return np
   else (verbMsgMLLn 2 $ "wap: " ++ show np) >> mlNewPacket
            >> waitUntilPacket (i+1) l


