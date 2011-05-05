#include "brep_to_xml.hxx"
#include <iostream>
#include <cstdlib>

using namespace std;

int main (int argc, char* argv[]) 
{
    char filename[50] = "./test/input.brp";
    if (argv[1] != NULL) {
	    strcpy(filename,argv[1]);
    }
        BrepToXML btx;
        btx.read_brep(filename);
                  
    
    
    return 0;
}
