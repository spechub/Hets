{-
Module      :  $Header$
Copyright   :  (c)  Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

   Utilities on top of HTk
-}

module GUI.HTkUtils where

import HTk

-- | create a window with title and list of options, return selected option
listBox :: String -> [String] -> IO (Maybe Int)
listBox title entries =
  do
    main <- createToplevel [text title]
    lb  <- newListBox main [value entries, bg "white", size (100, 50)] ::
             IO (ListBox String)
    pack lb [Side AtLeft, 
                 Expand On, Fill Both]
    scb <- newScrollBar main []
    pack scb [Side AtRight, Fill Y]
    lb # scrollbar Vertical scb
    (press, _) <- bindSimple lb (ButtonPress (Just 1))
    sync press
    sel <- getSelection lb
    destroy main
    return (case sel of
       Just [i] -> Just i
       _ -> Nothing)
