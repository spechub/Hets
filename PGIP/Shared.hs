{-# LANGUAGE CPP, DoAndIfThenElse #-}

module PGIP.Shared where

import Common.LibName
import Common.Json (Json (..), pJson)
import Logic.Comorphism (AnyComorphism)
import qualified Logic.Prover as LP
import Proofs.AbstractState (G_proof_tree, ProverOrConsChecker)
import Static.DevGraph

import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy.Char8 as BS
import Data.IORef
import Data.Time
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import Network.Wai
import Text.ParserCombinators.Parsec (parse)

#ifdef WARP1
type RsrcIO a = ResourceT IO a
#else
type RsrcIO a = IO a
#endif

data ProverMode = GlProofs | GlConsistency deriving (Show, Eq)

type ProofResult = (String, String, String, ProverOrConsChecker,
                -- (goalName, goalResult, goalDetails, prover,
                    AnyComorphism, Maybe (LP.ProofStatus G_proof_tree),
                -- comorphism, proofStatusM)
                    Maybe String)
                -- ConsistencyChecker output

data Session = Session
  { sessLibEnv :: LibEnv
  , sessLibName :: LibName
  , sessPath :: [String]
  , sessKey :: Int
  , sessStart :: UTCTime
  , lastAccess :: UTCTime
  , usage :: Int
  , sessCleanable :: Bool } deriving (Show)

type SessMap = Map.Map [String] Session
type Cache = IORef (IntMap.IntMap Session, SessMap)

parseJson :: String -> Maybe Json
parseJson s = case parse pJson "" s of
  Left _ -> Nothing
  Right json -> Just json

jsonBody :: BS.ByteString -> RsrcIO (Maybe Json)
jsonBody = return . parseJson . BS.unpack

receivedRequestBody :: Request -> RsrcIO B8.ByteString
receivedRequestBody = fmap (B8.pack . BS.unpack) . lazyRequestBody
