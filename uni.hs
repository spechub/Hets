
{-
In order to compile Hets with UniForM Workbench, use

#define UNI_PACKAGE 

in order to compile Hets without UniForM Workbench, use

#undef UNI_PACKAGE

and comment out the deifnition of HC_PACKAGE in the Makefile
-}

#define UNI_PACKAGE 
