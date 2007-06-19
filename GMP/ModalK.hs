module ModalK where

import GMPAS
import ModalLogic

instance ModalLogic ModalK where   
    parseIndex = return (ModalK ())
