
#include "brep_to_xml.hxx"
#include <iostream>
#include <cstdlib>

using namespace std;

void print_shape_type (TopoDS_Shape sh) 
{
    TopAbs_ShapeEnum st;
    st = sh.ShapeType();
    switch (st)
    {
        case TopAbs_COMPOUND:
            cout << "TopAbs_COMPOUND" << endl;
            break;
        case TopAbs_COMPSOLID:
            cout << "TopAbs_COMPSOLID" << endl;
            break;
        case TopAbs_SOLID:
            cout << "TopAbs_SOLID" << endl;
            break;
        case TopAbs_SHELL:
            cout << "TopAbs_SHELL" << endl;
            break;
        case TopAbs_FACE:
            cout << "TopAbs_FACE" << endl;
            break;
        case TopAbs_WIRE:
            cout << "TopAbs_WIRE" << endl;
            break;
        case TopAbs_EDGE:
            cout << "TopAbs_EDGE" << endl;
            break;
        case TopAbs_VERTEX:
            cout << "TopAbs_VERTEX" << endl;
            break;
        case TopAbs_SHAPE:
            cout << "TopAbs_SHAPE" << endl;
            break;
    }
}

int main (int argc, char* argv[]) 
{
    char filename[50] = "./test/input.brp";
    if (argv[1] != NULL) {
	    strcpy(filename,argv[1]);
    }
    TopoDS_Shape Sh;
    BRep_Builder builder;

    bool b = BRepTools::Read(Sh, (const Standard_CString)filename, builder);

    if (b) 
    {
        cout<< "reading ok" << endl;
        
        print_shape_type(Sh);
        BRepTools_ShapeSet SS;
        SS.Add(Sh);//A shapeSet cand help accessing subshapes of Sh.
        SS.Dump(Sh, std::cout);//says how many subshapes are in SS.
        cout << "############################################################"
             << endl;
        //SS.Dump(std::cout); //dumps the whole info.
        SS.DumpExtent(std::cout);//says how many shapes of each type are in SS
        cout << "############################################################"
        << endl;
        
        int i;
        TopoDS_Shape temp;
        for (i = 1; i <= SS.NbShapes(); i++)
        {
            temp = SS.Shape(i);
            print_shape_type(temp);
        }
                  
    }
    else 
    {
        cout<< "reading failure" << endl;
    }  
    
    
    return 0;
}
