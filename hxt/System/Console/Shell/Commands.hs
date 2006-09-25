{-# OPTIONS -fallow-undecidable-instances #-}
module System.Console.Shell.Commands where

import System.Console.Shell.Types
import System.Console.Shell.PPrint
import System.Console.Shell.Regex
import System.Console.Shell.ShellMonad


maybePrefix :: ShellDescription st -> String
maybePrefix desc = case commandStyle desc of CharPrefixCommands x -> [x]; _ -> ""

getShellCommands desc = map ($ desc) (shellCommands desc)


-- | Represents a command argument which is a filename
newtype File = File String

-- | Represents a command argument which is a username
newtype Username = Username String


-- | Represents a command argument which is an arbitrary
--   completable item.  The type argument determines the
--   instance of 'Completion' which is used to create
--   completions for this command argument.
newtype Completable compl = Completable String


------------------------------------------------------------------
-- | A typeclass representing user definable completion functions.


class Completion compl st | compl -> st where
  -- | Actually generates the list of possible completions, given the
  --   current shell state and a string representing the beginning of the word.
  complete :: compl -> (st -> String -> IO [String])

  -- | generates a label for the argument for use in the help displays.
  completableLabel :: compl -> String



-----------------------------------------------------------------------
-- | Prints the help message for this shell, which lists all avaliable
--   commands with their syntax and a short informative message about each.

showShellHelp :: ShellDescription st -> String

showShellHelp desc = show (commandHelpDoc desc (getShellCommands desc)) ++ "\n"


-------------------------------------------------------------------------
-- | Print the help message for a particular shell command

showCmdHelp :: ShellDescription st -> String -> String

showCmdHelp desc cmd =
  case cmds of
     [_] -> show (commandHelpDoc desc cmds) ++ "\n"
     _   -> show (text "bad command name: " <> squotes (text cmd)) ++ "\n"

 where cmds = filter (\ (n,_,_,_) -> n == cmd) (getShellCommands desc)


commandHelpDoc :: ShellDescription st ->  [(String,CommandParser st,Doc,Doc)] -> Doc

commandHelpDoc desc cmds =

   vcat [ (fillBreak 20 syn) <+> msg | (_,_,syn,msg) <- cmds ]


------------------------------------------------------------------------------
-- | Creates a shell command which will exit the shell.
exitCommand :: String            -- ^ the name of the command
            -> ShellCommand st
exitCommand name desc = ( name
                        , \_ -> [CompleteParse (shellSpecial ShellExit)]
                        , text (maybePrefix desc) <> text name
                        , text "Exit the shell"
                        )


--------------------------------------------------------------------------
-- | Creates a command which will print the shell help message.
helpCommand :: String           -- ^ the name of the command
            -> ShellCommand st
helpCommand name desc = ( name
                        , \_ -> [CompleteParse (shellSpecial (ShellHelp Nothing))]
                        , text (maybePrefix desc) <> text name
                        , text "Display the shell command help"
                        )


---------------------------------------------------------
-- | Creates a command to toggle a boolean value
toggle :: String                -- ^ command name
       -> String                -- ^ help message
       -> (st -> Bool)          -- ^ getter
       -> (Bool -> st -> st)    -- ^ setter
       -> ShellCommand st

toggle name helpMsg getter setter desc =
     ( name
     , \_ -> [CompleteParse doToggle]
     , text (maybePrefix desc) <> text name
     , text helpMsg
     )

  where doToggle = do
          st <- getShellSt
          if getter st 
             then shellPutInfoLn (name++" off") >> putShellSt (setter False st)
             else shellPutInfoLn (name++" on")  >> putShellSt (setter True  st)

-------------------------------------------------------------------
-- | Creates a user defined shell commmand.  This relies on the
--   typeclass machenery defined by 'CommandFunction'.
cmd :: CommandFunction f st
    => String           -- ^ the name of the command
    -> f                -- ^ the command function.  See 'CommandFunction' for restrictions
                        --   on the type of this function.
    -> String           -- ^ the help string for this command
    -> ShellCommand st


cmd name f helpMsg desc =
      ( name
      , parseCommand (wordBreakChars desc) f
      , text (maybePrefix desc) <> text name <+> hsep (commandSyntax f)
      , text helpMsg
      )


------------------------------------------------------------------------------
-- | This class is used in the 'cmd' function to automaticly generate
--   the command parsers and command syntax strings for user defined
--   commands.  The type of \'f\' is restricted to have a restricted set of
--   monomorphic arguments ('Bool', 'Int', 'Integer', 'Float', 'Double', 'String',
--   'File', 'Username', and 'Completable') and the head type must be @Sh st ()@
--
-- >  f :: Int -> File -> Sh MyShellState ()
-- >  g :: Double -> Sh st ()
-- >  h :: Sh SomeShellState ()
--
--   are all legal types, whereas:
-- 
-- >  bad1 :: a -> Sh (MyShellState a) ()
-- >  bad2 :: [Int] -> Sh MyShellState ()
-- >  bad3 :: Bool -> MyShellState
--
--   are not.

class CommandFunction f st | f -> st where
  parseCommand  :: String -> f -> CommandParser st
  commandSyntax :: f -> [Doc]


-------------------------------------------------------------
-- Instances for the base case

instance CommandFunction (Sh st ()) st where
  parseCommand wbc m str =
         do (x,[]) <- runRegex (maybeSpaceBefore (Epsilon (CompleteParse m))) str
            return x

  commandSyntax _ = []

--------------------------------------------------------------
-- Instances for the supported command argument types

instance CommandFunction r st
      => CommandFunction (Int -> r) st where
  parseCommand = doParseCommand Nothing intRegex id
  commandSyntax f = text (show intRegex) : commandSyntax (f undefined)

instance CommandFunction r st
      => CommandFunction (Integer -> r) st where
  parseCommand = doParseCommand Nothing intRegex id
  commandSyntax f =  text (show intRegex) : commandSyntax (f undefined)

instance CommandFunction r st
      => CommandFunction (Float -> r) st where
  parseCommand = doParseCommand Nothing floatRegex id
  commandSyntax f = text (show floatRegex) : commandSyntax (f undefined)

instance CommandFunction r st
      => CommandFunction (Double -> r) st where
  parseCommand = doParseCommand Nothing floatRegex id
  commandSyntax f = text (show floatRegex) : commandSyntax (f undefined)

instance CommandFunction r st
      => CommandFunction (String -> r) st where
  parseCommand wbc = doParseCommand Nothing (wordRegex wbc) id wbc
  commandSyntax f = text (show (wordRegex "")) : commandSyntax (f undefined)

instance CommandFunction r st
      => CommandFunction (File -> r) st where
  parseCommand wbc = doParseCommand
                        (Just FilenameCompleter)
                        (wordRegex wbc)
                        File
                        wbc
  commandSyntax f = text "<file>" : commandSyntax (f undefined)

instance CommandFunction r st
      => CommandFunction (Username -> r) st where
  parseCommand wbc = doParseCommand
                        (Just UsernameCompleter)
                        (wordRegex wbc)
                        Username
                        wbc
  commandSyntax f = text "<username>" : commandSyntax (f undefined)

instance (CommandFunction r st,Completion compl st)
      => CommandFunction (Completable compl -> r) st where
  parseCommand wbc = doParseCommand
                        (Just (OtherCompleter (complete (undefined::compl))))
                        (wordRegex wbc)
                        Completable
                        wbc
  commandSyntax f = text (completableLabel (undefined::compl)) : commandSyntax (f undefined)


----------------------------------------------------------------
-- Helper functions used in the above instance declarations
-- These make use of the hackish regex library.

doParseCommand compl re proj wbc f []  = return (IncompleteParse compl)
doParseCommand compl re proj wbc f str =
  let xs = runRegex (maybeSpaceBefore (maybeSpaceAfter re)) str
  in case xs of
        [] -> return (IncompleteParse compl)
        _  -> do (x,str') <- xs; parseCommand wbc (f (proj x)) str'

commandsRegex :: ShellDescription st -> Regex Char (String,CommandParser st,Doc,Doc)
commandsRegex desc =
   case commandStyle desc of
      CharPrefixCommands ch -> prefixCommandsRegex ch (getShellCommands desc)
      OnlyCommands          -> onlyCommandsRegex      (getShellCommands desc)
      SingleCharCommands    -> singleCharCommandRegex (getShellCommands desc)

onlyCommandsRegex :: [(String,CommandParser st,Doc,Doc)] -> Regex Char (String,CommandParser st,Doc,Doc)
onlyCommandsRegex xs =
    Concat (\_ x -> x) maybeSpaceRegex $
    Concat (\x _ -> x) (anyOfRegex (map (\ (x,y,z,w) -> (x,(x,y,z,w))) xs)) $
                       spaceRegex

prefixCommandsRegex :: Char -> [(String,CommandParser st,Doc,Doc)] -> Regex Char (String,CommandParser st,Doc,Doc)
prefixCommandsRegex ch xs =
    Concat (\_ x -> x) maybeSpaceRegex $
    Concat (\_ x -> x) (strTerminal ch) $
    Concat (\x _ -> x) (anyOfRegex (map (\ (x,y,z,w) -> (x,(x,y,z,w))) xs)) $
                       spaceRegex

singleCharCommandRegex :: [(String,CommandParser st,Doc,Doc)] -> Regex Char (String,CommandParser st,Doc,Doc)
singleCharCommandRegex xs =
    altProj
       (anyOfRegex (map (\ (x,y,z,w) -> ([head x],(x,y,z,w))) xs))
       (Epsilon ("",\_ -> [CompleteParse (shellSpecial ShellNothing)],empty,empty))
