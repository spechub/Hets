module System.Console.Shell.ConsoleHandler
( withControlCHandler
) where

import qualified Control.Exception as Ex
import qualified System.Posix.Signals as PS

withControlCHandler :: IO () -> IO a -> IO a
withControlCHandler hdl m =
  Ex.bracket
      (PS.installHandler PS.keyboardSignal (PS.Catch hdl) Nothing)
      (\oldh -> PS.installHandler PS.keyboardSignal oldh Nothing)
      (\_ -> m)
