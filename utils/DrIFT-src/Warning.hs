module Warning where

{-
#if defined(__NHC__)
import NonStdTrace
#else
import Trace
#endif

warning = trace
-}

warning s x = x
