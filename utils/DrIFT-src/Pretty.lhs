\begin{code}
module Pretty (module Text.PrettyPrint.HughesPJ, tshow) where
import Text.PrettyPrint.HughesPJ
tshow :: Show a => a -> Doc
tshow n = text (show n)
\end{code}


