#include "brep_to_xml.hxx"
#include <iostream>
#include <cstdlib>
#include <string>
using namespace std;

int main (int argc, char* argv[]) 
{
    char filename[50] = "./test/input.brp";
    if (argv[1] != NULL) {
	    strcpy(filename,argv[1]);
    }
        if(string(argv[2]) == "rectangle")
        {
            BrepToXML btx;
            btx.read_brep(filename);
            btx.build_graph();
            btx.build_xml();
        }

        //TODO locations, locations
    
    return 0;
}
