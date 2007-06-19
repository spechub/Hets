FLAGS = #-Wall
OBJS = GMPAS.o GMPParser.o ModalLogic.o Main.o ModalK.o ModalKD.o GradedML.o GenericML.o CoalitionL.o Lexer.o GMPSAT.o
ITF = GMPAS.hi GMPParser.hi ModalLogic.hi Main.hi ModalK.hi ModalKD.hi GradedML.hi GenericML.hi CoalitionL.hi Lexer.hi GMPSAT.hi
CC = ghc
LD = --make
RM = rm -rf

all: Main.hs GMPAS.hs GMPParser.hs ModalLogic.hs ModalK.hs ModalKD.hs GradedML.hs GenericML.hs CoalitionL.hs Lexer.hs GMPSAT.hs
	$(CC) $(LD) $(FLAGS) Main.hs 

clean: 
	$(RM) $(OBJS) $(ITF) Main

