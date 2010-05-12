
import qualified CASL.Sign as CSign
import qualified Driver.AnaLib as AnaLib
import qualified Driver.Options as Options
import qualified Data.Map as Map

baseCASLSig :: CSign.CASLSig
baseCASLSig =
  where Just (libname,lib) = unsafePerformIO $ AnaLib.anaLib Options.defaultHetcatsOpts "CommonLogic/CommonLogic.casl" 
        dgraph = head (Map.elems lib)
        body = dgBody dgraph