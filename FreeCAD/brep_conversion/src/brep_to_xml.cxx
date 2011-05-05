
#include "brep_to_xml.hxx"
#include <iostream>
#include <cstdlib>
#include <Standard_PrimitiveTypes.hxx>

using namespace std;
/*******************************************************************************
 *
 *Constructor and destructor for BrepToXML class
 *
 ******************************************************************************/

BrepToXML::BrepToXML() {}

BrepToXML::BrepToXML(TopoDS_Shape shape)
{
    Sh = shape;
    SS.Add(Sh);
}

BrepToXML::BrepToXML(const BrepToXML& btxml)
{
    Sh = btxml.Sh;
    SS.Add(Sh);
}

BrepToXML::~BrepToXML() {}

/*
 *setter and getter for the contained shape
 */
TopoDS_Shape BrepToXML::get_shape(void)
{
    return Sh;
}
void BrepToXML::set_shape(TopoDS_Shape shape)
{
    Sh = shape;
    //TODO Refresh the shapeset
}


/*******************************************************************************
 *
 * method to print the type of the contained shape
 *
 ******************************************************************************/

void BrepToXML::print_shape_type() 
{
    TopAbs_ShapeEnum st;
    st = Sh.ShapeType();
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

/*******************************************************************************
 *
 * method to read from a .brp file given the filepath as a c_string
 *
 ******************************************************************************/


bool BrepToXML::read_brep(const char* filePath)
{
    bool b = BRepTools::Read(Sh, (const Standard_CString)filePath, builder);
    //insert testing guards
    if (b)
    {
        cout << "reading ok" << endl;
    }
    else
    {
        cout << "error while reading brep file" << endl;
    }
    return b;
}

/*******************************************************************************
 *
 * method to print the subshapes of the contained shape
 * 
 ******************************************************************************/
void BrepToXML::print_subshapes()
{
    vector <TopoDS_Shape> list;
    list = this->get_subshapes();
    //TODO cout part for each shape in vector
}

/*******************************************************************************
 *
 * method to print the value of the contained shape's location
 *
 ******************************************************************************/
void BrepToXML::print_location()
{
    //TODO
    cout << "location" << endl;
}

/*******************************************************************************
 * 
 *return a vector containing the subshapes only
 *
 ******************************************************************************/
vector <TopoDS_Shape> BrepToXML::get_subshapes(void)
{
    vector <TopoDS_Shape> temp;
    if (SS.NbShapes() > 1)
    {
        for (int i = 2; i <= SS.NbShapes(); i++)
        {
            temp.push_back(SS.Shape(i));
        }
    }
    else
    {
        cout << "error -- no subshapes" << endl;
    }
    return temp;
}


void BrepToXML::build_graph(void)
{

}
















