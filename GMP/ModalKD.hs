module ModalKD where

import GMPAS
import ModalLogic

instance ModalLogic ModalKD where
    parseIndex = return (ModalKD ())
