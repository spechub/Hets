module Shell.ConsoleHandler
( withControlCHandler
) where

import qualified Control.Exception as Ex

-- #ifndef mingw32_HOST_OS

import qualified System.Posix.Signals as PS

withControlCHandler :: IO () -> IO a -> IO a
withControlCHandler hdl m =
  Ex.bracket
      (PS.installHandler PS.keyboardSignal (PS.Catch hdl) Nothing)
      (\oldh -> PS.installHandler PS.keyboardSignal oldh Nothing)
      (\_ -> m)

-- #else

{-- import qualified GHC.ConsoleHandler as CH


handleCtrlC :: IO () -> CH.Handler
handleCtrlC hdl = CH.Catch $ \ev ->
   case ev of
     CH.ControlC -> hdl
     _           -> return ()


withControlCHandler :: IO () -> IO a -> IO a
withControlCHandler hdl m =
  Ex.bracket
      (CH.installHandler (handleCtrlC hdl))
      (\oldh -> CH.installHandler oldh)
      (\_ -> m)

--}
-- #endif
