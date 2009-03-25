{-# OPTIONS -fglasgow-exts #-}

module ModalCasl where

import Control.Monad (liftM, liftM2)
import Text.ParserCombinators.Parsec hiding (State)


{------------------------------------------------------------------------------}
{-                                                                            -}
{-  Formulas of Modal CASL                                                    -}
{-                                                                            -}
{------------------------------------------------------------------------------}


data StateFormula a =  Var a
                    -- Boolean Operators
                    |  Snot        (StateFormula a)
                    |  Sand        (StateFormula a) (StateFormula a)
                    |  Sor         (StateFormula a) (StateFormula a)
                    -- Path Quantifiers
                    |  E           (PathFormula a)
                    |  A           (PathFormula a)
                    -- Future Modalities
                    |  Diamond     (StateFormula a)
                    |  Box         (StateFormula a)
                    -- Past Modalities
                    |  DiamondPast (StateFormula a)
                    |  BoxPast     (StateFormula a)
                    -- Fixpoint Opertors
                    |  Mu a        (StateFormula a)
                    |  Nu a        (StateFormula a)


data PathFormula a  =  State  (StateFormula a)
                    -- Boolean Operators
                    |  Pnot   (PathFormula a)
                    |  Pand   (PathFormula a) (PathFormula a)
                    |  Por    (PathFormula a) (PathFormula a)
                    -- Future Temporal Operators
                    |  X      (PathFormula a)
                    |  G      (PathFormula a)
                    |  F      (PathFormula a)
                    |  W      (PathFormula a) (PathFormula a)
                    |  U      (PathFormula a) (PathFormula a)
                    |  B      (PathFormula a) (PathFormula a)
                    |  W'     (PathFormula a) (PathFormula a)
                    |  U'     (PathFormula a) (PathFormula a)
                    |  B'     (PathFormula a) (PathFormula a)
                    -- Past Temporal Operators
                    |  XPast  (PathFormula a)
                    |  GPast  (PathFormula a)
                    |  FPast  (PathFormula a)
                    |  WPast  (PathFormula a) (PathFormula a)
                    |  UPast  (PathFormula a) (PathFormula a)
                    |  BPast  (PathFormula a) (PathFormula a)
                    |  XPast' (PathFormula a)
                    |  WPast' (PathFormula a) (PathFormula a)
                    |  UPast' (PathFormula a) (PathFormula a)
                    |  BPast' (PathFormula a) (PathFormula a)


instance (Show a) => Show (StateFormula a) where
  show phi =  showStateFormula phi True


instance (Show a) => Show (PathFormula  a) where
  show phi =  showPathFormula phi  True


showStateFormula (Var x)               outer =  show x
showStateFormula (Snot        phi)     outer =  "not " ++ showStateFormula phi False
showStateFormula (Sand        phi psi) True  =  showStateFormula phi False ++ " /\\ " ++ showStateFormula psi False
showStateFormula (Sor         phi psi) True  =  showStateFormula phi False ++ " \\/ " ++ showStateFormula psi False
showStateFormula (E           phi)     outer =  "E " ++ showPathFormula phi False
showStateFormula (A           phi)     outer =  "A " ++ showPathFormula phi False
showStateFormula (Diamond     phi)     True  =  "<> " ++ showStateFormula phi False
showStateFormula (Box         phi)     True  =  "[] " ++ showStateFormula phi False
showStateFormula (DiamondPast phi)     True  =  "<~> " ++ showStateFormula phi False
showStateFormula (BoxPast     phi)     True  =  "[~] " ++ showStateFormula phi False
showStateFormula (Mu x        phi)     True  =  "mu " ++ show x ++ " . " ++ showStateFormula phi False
showStateFormula (Nu x        phi)     True  =  "nu " ++ show x ++ " . " ++ showStateFormula phi False
showStateFormula phi                   False =  "(" ++ showStateFormula phi True ++ ")"


showPathFormula  (State       phi)     outer =  showStateFormula phi outer
showPathFormula  (Pnot        phi)     outer =  "not " ++ showPathFormula phi False
showPathFormula  (Pand        phi psi) True  =  showPathFormula phi False ++ " /\\ " ++ showPathFormula psi False
showPathFormula  (Por         phi psi) True  =  showPathFormula phi False ++ " \\/ " ++ showPathFormula psi False
showPathFormula  (X           phi)     outer =  "X " ++ showPathFormula phi False
showPathFormula  (G           phi)     outer =  "G " ++ showPathFormula phi False
showPathFormula  (F           phi)     outer =  "F " ++ showPathFormula phi False
showPathFormula  (W           phi psi) True  =  showPathFormula phi False ++ " W " ++ showPathFormula psi False
showPathFormula  (U           phi psi) True  =  showPathFormula phi False ++ " U " ++ showPathFormula psi False
showPathFormula  (B           phi psi) True  =  showPathFormula phi False ++ " B " ++ showPathFormula psi False
showPathFormula  (W'          phi psi) True  =  showPathFormula phi False ++ " W! " ++ showPathFormula psi False
showPathFormula  (U'          phi psi) True  =  showPathFormula phi False ++ " U! " ++ showPathFormula psi False
showPathFormula  (B'          phi psi) True  =  showPathFormula phi False ++ " B! " ++ showPathFormula psi False
showPathFormula  (XPast       phi)     outer =  "~X " ++ showPathFormula phi False
showPathFormula  (GPast       phi)     outer =  "~G " ++ showPathFormula phi False
showPathFormula  (FPast       phi)     outer =  "~F " ++ showPathFormula phi False
showPathFormula  (WPast       phi psi) True  =  showPathFormula phi False ++ " ~W " ++ showPathFormula psi False
showPathFormula  (UPast       phi psi) True  =  showPathFormula phi False ++ " ~U " ++ showPathFormula psi False
showPathFormula  (BPast       phi psi) True  =  showPathFormula phi False ++ " ~B " ++ showPathFormula psi False
showPathFormula  (XPast'      phi)     outer =  "~X! " ++ showPathFormula phi False
showPathFormula  (WPast'      phi psi) True  =  showPathFormula phi False ++ " ~W! " ++ showPathFormula psi False
showPathFormula  (UPast'      phi psi) True  =  showPathFormula phi False ++ " ~U! " ++ showPathFormula psi False
showPathFormula  (BPast'      phi psi) True  =  showPathFormula phi False ++ " ~B! " ++ showPathFormula psi False
showPathFormula  phi                   False =  "(" ++ showPathFormula phi True ++ ")"


{------------------------------------------------------------------------------}


parser :: Parser a -> Parser (StateFormula a)
parser var = between spaces eof stateImpl where

        stateImpl =  chainl1 stateOr (do string "->"
                                         spaces
                                         return (Sor . Snot))

        stateOr =  chainl1 stateAnd (do string "\\/"
                                        spaces
                                        return Sor)

        stateAnd =  chainl1 state (do string "/\\"
                                      spaces
                                      return Sand)

        state =  (do char '('
                     spaces
                     x <- stateImpl
                     char ')'
                     spaces
                     return x)
             <|> (do string "not"
                     spaces
                     liftM Snot state)
             <|> (do string "E"
                     spaces
                     liftM E pathImpl)
             <|> (do string "A"
                     spaces
                     liftM A pathImpl)
             <|> (do x <- string "<"
                     y <- option "" (string "~")
                     z <- string ">"
                     spaces
                     case concat [x, y, z] of
                          "<>"  -> liftM Diamond state
                          "<~>" -> liftM DiamondPast state)
             <|> (do x <- string "["
                     y <- option "" (string "~")
                     z <- string "]"
                     spaces
                     case concat [x, y, z] of
                          "[]"  -> liftM Box state
                          "[~]" -> liftM BoxPast state)
             <|> (do string "mu"
                     space
                     spaces
                     x <- var
                     spaces
                     char '.'
                     spaces
                     liftM (Mu x) stateImpl)
             <|> (do string "nu"
                     space
                     spaces
                     x <- var
                     spaces
                     char '.'
                     spaces
                     liftM (Nu x) stateImpl)
             <|> (do x <- var
                     spaces
                     return (Var x))


        pathImpl =  chainl1 pathOr (do string "->"
                                       spaces
                                       return (Por . Pnot))

        pathOr =  chainl1 pathAnd (do string "\\/"
                                      spaces
                                      return Por)

        pathAnd =  chainl1 pathBinary (do string "/\\"
                                          spaces
                                          return Pand)

        pathBinary = chainl1 pathUnary $ (do x <- option "" (string "~")
                                             y <- (string "W" <|> string "U" <|> string "B")
                                             z <- option "" (string "!")
                                             spaces
                                             case concat [x, y, z] of
                                                  "W"   -> return W
                                                  "U"   -> return U
                                                  "B"   -> return B
                                                  "W!"  -> return W'
                                                  "U!"  -> return U'
                                                  "B!"  -> return B'
                                                  "~W"  -> return WPast
                                                  "~U"  -> return UPast
                                                  "~B"  -> return BPast
                                                  "~W!" -> return WPast'
                                                  "~U!" -> return UPast'
                                                  "~B!" -> return BPast')

        pathUnary =  (do char '('
                         spaces
                         x <- pathImpl
                         char ')'
                         spaces
                         return x)
                 <|> (do string "not"
                         spaces
                         liftM Pnot pathUnary)
                 <|> (do x <- option "" (string "~")
                         y <- (string "X" <|> string "G" <|> string "F")
                         z <- if concat [x, y] == "~X" then option "" (string "!")
                                                       else return ""
                         spaces
                         case concat [x, y, z] of
                              "X"   -> liftM X      pathUnary
                              "G"   -> liftM G      pathUnary
                              "F"   -> liftM F      pathUnary
                              "~X"  -> liftM XPast  pathUnary
                              "~G"  -> liftM GPast  pathUnary
                              "~F"  -> liftM FPast  pathUnary
                              "~X!" -> liftM XPast' pathUnary)
                 <|> liftM State state


{------------------------------------------------------------------------------}
