
{- HetCATS/hetcats/Options.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   A datatype for options and a list of options hetcats understands.

-}

module Options where

import GetOpt

data Flag = Verbose
	  | Version
	  | InTypes  InType
	  | OutFlags [OutFlag] 
	  | Analysis [AnaFlag]

data InType = SML_Gen_ATerm [ATFlags] | CaslIn

data ATFlags = BAF | TAF | TRM

data OutFlag = LaTeX | CaslOut | Casl0 | Global_Env [GE_Type]

data AnaFlag = Static

data GE_Type = ATerm_TAF | ATerm_TRM | XML

options :: [OptDescr Flag]
options =
 [ Option ['v']     ["verbose"] (NoArg Verbose)       "chatty output on stderr"
 , Option ['V']     ["version"] (NoArg Version)       "show version number"
{- , Option ['i']     ["input-type"]  (OpIn)  "output FILE"
 , Option ['c']     []          (OptArg inp  "FILE")  "input FILE"
 , Option ['L']     ["libdir"]  (ReqArg LibDir "DIR") "library directory"-}
 ]

hetcatsOpts :: [String] -> IO ([Flag], [String])
hetcatsOpts argv =
   case (getOpt Permute options argv) of
      (o,n,[]  ) -> return (o,n)
      (_,_,errs) -> fail (concat errs ++ usageInfo header options)
  where header = "Usage: hetcats [OPTION...] files..."
