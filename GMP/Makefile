FLAGS = #-Wall
OBJS = GMPAS.o GMPParser.o ModalLogic.o Main.o ModalK.o ModalKD.o ModalInt.o ModalKar.o ModalBS.o Lexer.o GMPSAT.o
ITF = GMPAS.hi GMPParser.hi ModalLogic.hi Main.hi ModalK.hi ModalKD.hi ModalInt.hi ModalKar.hi ModalBS.hi Lexer.hi GMPSAT.hi
CC = ghc
LD = --make
RM = rm -rf

all: Main.hs GMPAS.hs GMPParser.hs ModalLogic.hs ModalK.hs ModalKD.hs ModalInt.hs ModalKar.hs ModalBS.hs Lexer.hs GMPSAT.hs
	$(CC) $(LD) $(FLAGS) Main.hs 

clean: 
	$(RM) $(OBJS) $(ITF) Main

