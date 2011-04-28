 
CC=g++
CFLAGS=-Wall -W
LFLAGS=
VERSION=debug
TARGET=brep_to_xml

SRCS=$(VERSION)/src
BIN=$(VERSION)/bin
OBJS=$(BIN)/obj
INCLUDE=$(VERSION)/include/opencascade

all: $(TARGET)

$(TARGET): $(OBJS)/brep_to_xml.o
	$(CC) $(CFLAGS) $(LFLAGS) $^ -I $(INCLUDE) -o $(BIN)/$(TARGET)

$(OBJS)/brep_to_xml.o: $(SRCS)/brep_to_xml.cxx
	$(CC) $(CFLAGS) $(LFLAGS) -I $(INCLUDE) -c $^
	mv $(@F) $(OBJS)/

clean:
	-rm $(BIN)/$(TARGET)
	-rm $(OBJS)/*.o