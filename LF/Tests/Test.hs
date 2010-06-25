{- |
Description :  Test file for Sign
-}

import LF.Sign
import LF.Morphism
import Common.Doc
import Common.DocUtils
import qualified Data.Map as Map
import qualified Data.Set as Set
import LF.Twelf2DG
import System.Directory
import Network.URI
import Static.DevGraph

import Text.XML.Light.Input
import Text.XML.Light.Types
import Text.XML.Light.Proc

import System.Exit
import System.IO
import System.Process
import System.FilePath
import Common.LibName
import Common.Utils
import Common.Id

test :: [Symbol]
test = [ Symbol {symBase = "/home/mathias/hets/Framework/specs/logics/propositional/syntax/base", symModule = "Base", symName = "o"},
         Symbol {symBase = "/home /mathias/hets/Framework/specs/logics/propositional/syntax/base", symModule = "Base", symName = "ded"} ]



  
