 
CC=g++
CFLAGS=-Wall
LFLAGS=
TARGET=brep_to_xml

SRCS=src
BIN=bin
OBJS=objs
INCLUDE=/usr/include/opencascade

# g++ brep_to_xml.cxx -I /usr/include/opencascade/ -Wall -lTKBRep

all: $(TARGET)

$(TARGET): $(OBJS)/brep_to_xml.o
	$(CC) $(CFLAGS) $(LFLAGS) $^ -I $(INCLUDE) -lTKBRep -o $(BIN)/$(TARGET)

$(OBJS)/brep_to_xml.o: $(SRCS)/brep_to_xml.cxx
	$(CC) $(CFLAGS) $(LFLAGS) -I $(INCLUDE) -lTKBRep -c $^
	mv $(@F) $(OBJS)/

clean:
	-rm $(BIN)/$(TARGET)
	-rm $(OBJS)/*.o
