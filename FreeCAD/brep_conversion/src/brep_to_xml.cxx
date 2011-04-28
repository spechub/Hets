
#include "brep_to_xml.hxx"

using namespace std;

int main (int argc, char* argv[]) {
  char* filename = "input.brp";
  if (argv[1] != NULL) {
	strcpy(filename,argv[1]);
  }
  TopoDS_Shape Sh;
  BRep_Builder builder;

  BRepTools::Read(Sh, (const Standard_CString)filename, builder);
  return 0;
}
