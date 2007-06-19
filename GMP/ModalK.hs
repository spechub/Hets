module ModalK where

import ModalLogic
import GMPAS

instance ModalLogic ModalK where 
    parseIndex = return (ModalK ())
