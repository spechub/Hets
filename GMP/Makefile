FLAGS = #-Wall
OBJS = GMPAS.o GMPParser.o Main.o
ITF = GMPAS.hi GMPParser.hi Main.hi
CC = ghc
LD = --make
RM = rm -rf

all: Main.hs GMPAS.hs GMPParser.hs
	$(CC) $(LD) $(FLAGS) Main.hs -fglasgow-exts

clean: 
	$(RM) $(OBJS) $(ITF) Main

