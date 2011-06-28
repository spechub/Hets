 
CC=g++
CFLAGS=-Wall -I/usr/include/libxml2 -I/usr/include/opencascade

LFLAGS= -lTKBRep -lxml2
TARGET=brep_to_xml

SRCS=src
BIN=bin
OBJS=objs

# g++ brep_to_xml.cxx -I /usr/include/opencascade/ -Wall -lTKBRep

all: $(TARGET)

$(TARGET): $(OBJS)/brep_to_xml.o $(OBJS)/main.o
	$(CC) $^ $(CFLAGS) $(LFLAGS) -o $(BIN)/$(TARGET)

$(OBJS)/brep_to_xml.o: $(SRCS)/brep_to_xml.cxx
	$(CC) $(CFLAGS) $(LFLAGS) -c $^
	mv $(@F) $(OBJS)/
	
$(OBJS)/main.o: $(SRCS)/main.cxx
	$(CC) $(CFLAGS) $(LFLAGS) -c $^
	mv $(@F) $(OBJS)/

clean:
	-rm $(BIN)/$(TARGET)
	-rm $(OBJS)/*.o
