{-# OPTIONS -fglasgow-exts #-}

module ModalCasl where



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
  show phi =  show' phi True where
    show' (Var x)               outer =  show x
    show' (Snot        phi)     outer =  "not " ++ show' phi False
    show' (Sand        phi psi) True  =  show' phi False ++ " /\\ " ++ show' psi False
    show' (Sor         phi psi) True  =  show' phi False ++ " \\/ " ++ show' psi False
    show' (E           phi)     outer =  "E " ++ show phi
    show' (A           phi)     outer =  "A " ++ show phi
    show' (Diamond     phi)     True  =  "<> " ++ show' phi False
    show' (Box         phi)     True  =  "[] " ++ show' phi False
    show' (DiamondPast phi)     True  =  "<~> " ++ show' phi False
    show' (BoxPast     phi)     True  =  "[~] " ++ show' phi False
    show' (Mu x        phi)     True  =  "mu " ++ show x ++ " . " ++ show' phi False
    show' (Nu x        phi)     True  =  "nu " ++ show x ++ " . " ++ show' phi False
    show' phi                   False =  "(" ++ show' phi True ++ ")"


instance (Show a) => Show (PathFormula a) where
  show phi =  show' phi True where
    show' (State  phi)     True  =  show phi
    show' (Pnot   phi)     outer =  "not " ++ show' phi False
    show' (Pand   phi psi) True  =  show' phi False ++ " /\\ " ++ show' psi False
    show' (Por    phi psi) True  =  show' phi False ++ " \\/ " ++ show' psi False
    show' (X      phi)     outer =  "X " ++ show' phi False
    show' (G      phi)     outer =  "G " ++ show' phi False
    show' (F      phi)     outer =  "F " ++ show' phi False
    show' (W      phi psi) True  =  show' phi False ++ " W " ++ show' psi False
    show' (U      phi psi) True  =  show' phi False ++ " U " ++ show' psi False
    show' (B      phi psi) True  =  show' phi False ++ " B " ++ show' psi False
    show' (W'     phi psi) True  =  show' phi False ++ " W! " ++ show' psi False
    show' (U'     phi psi) True  =  show' phi False ++ " U! " ++ show' psi False
    show' (B'     phi psi) True  =  show' phi False ++ " B! " ++ show' psi False
    show' (XPast  phi)     outer =  "~X " ++ show' phi False
    show' (GPast  phi)     outer =  "~G " ++ show' phi False
    show' (FPast  phi)     outer =  "~F " ++ show' phi False
    show' (WPast  phi psi) True  =  show' phi False ++ " ~W " ++ show' psi False
    show' (UPast  phi psi) True  =  show' phi False ++ " ~U " ++ show' psi False
    show' (BPast  phi psi) True  =  show' phi False ++ " ~B " ++ show' psi False
    show' (XPast' phi)     outer =  "~X! " ++ show' phi False
    show' (WPast' phi psi) True  =  show' phi False ++ " ~W! " ++ show' psi False
    show' (UPast' phi psi) True  =  show' phi False ++ " ~U! " ++ show' psi False
    show' (BPast' phi psi) True  =  show' phi False ++ " ~B! " ++ show' psi False
    show' phi              False =  "(" ++ show' phi True ++ ")"


{------------------------------------------------------------------------------}
