{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (cpp)

Utilities on top of HTk or System.IO
-}

module GUI.Utils (listBox, createTextSaveDisplay, askFileNameAndSave) where

#ifdef UNI_PACKAGE
import GUI.HTkUtils (listBox, createTextSaveDisplay, askFileNameAndSave)
#else
import GUI.ConsoleUtils (listBox, createTextSaveDisplay, askFileNameAndSave)
#endif
