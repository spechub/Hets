module ModalKD where

import ModalLogic
import GMPAS

instance ModalLogic ModalKD where 
    parseIndex = return (ModalKD ())
