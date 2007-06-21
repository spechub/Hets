module ModalKD where

import GMPAS
import ModalLogic

instance ModalLogic ModalKD KDrules where
    parseIndex = return (ModalKD ())

-------------------------------------------------------------------------------
