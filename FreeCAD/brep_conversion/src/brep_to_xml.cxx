
#include "brep_to_xml.hxx"
#include <iostream>
#include <cstdlib>

using namespace std;

int main (int argc, char* argv[]) {
  char* filename = "input.brp";
  if (argv[1] != NULL) {
	strcpy(filename,argv[1]);
  }
  TopoDS_Shape Sh;
  BRep_Builder builder;

  bool b = BRepTools::Read(Sh, (const Standard_CString)filename, builder);

  if (b) {
    cout<< "reading ok";
  }
  else {
    cout<< "reading failure";
  }
  cout<< endl;

  return 0;
}
