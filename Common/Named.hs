module Common.Named where

data Named s = NamedSen { senName  :: String,
                          sentence :: s }
	       deriving (Eq,Show)
