
#include "brep_to_xml.hxx"
#include <iostream>
#include <cstdlib>
#include <Standard_PrimitiveTypes.hxx>
#include <TopTools_LocationSet.hxx>
#include <BRep_Tool.hxx>

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

void BrepToXML::print_shape_type(TopoDS_Shape a) 
{
    TopAbs_ShapeEnum st;
    st = a.ShapeType();
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
    SS.Add(Sh);
    return b;
}

/*******************************************************************************
 *
 * method to print the subshapes of the contained shape
 * 
 ******************************************************************************/
void BrepToXML::print_subshapes()
{
    for (int i = 0; i < SS.NbShapes(); i++)
    {
        this->print_shape_type(SS.Shape(i+1));
        
        
       // cout << SS.Locations().Location(i+1) << endl;
    }
}


/*******************************************************************************
 * 
 *return a vector containing the subshapes only
 *
 *  arg == 0  => the vector includes the container shape
 *  arg == 1  => it does not
 *  arg > 1   => lose data
 ******************************************************************************/
vector <TopoDS_Shape> BrepToXML::get_subshapes(int arg)
{   
    vector <TopoDS_Shape> temp;       
    if (SS.NbShapes() > arg)
    {
        for (int i = arg+1; i <= SS.NbShapes(); i++)
        {
           // temp.push_back(SS.Shape(i+1));
        }
    }
    else
    {
        cout << "error -- no subshapes" << endl;
    }

    return temp;
}

/*******************************************************************************
 *
 * initializer for the graph matrix
 *
 ******************************************************************************/
void BrepToXML::init_graph(void)
{
    vector <int> line;
    for (int i = 0; i < SS.NbShapes(); i++)
    {
        for (int j = 0; j < SS.NbShapes(); j++)
        {
            line.push_back(0);
        }
        graph.push_back(line);
        line.clear();
    }
}

/*******************************************************************************
 *
 * method to build the dependency graph for the shapeset
 *
 ******************************************************************************/
void BrepToXML::build_graph(void)
{
    this->init_graph();
    this->add_to_graph();
    this->simplify_graph();
}



void BrepToXML::add_to_graph()
{
   
    BRepTools_ShapeSet tempss;
    for (int i = 1; i <= SS.NbShapes(); i++)
    {
        tempss.Add(SS.Shape(i));
        for (int j = 1; j <= tempss.NbShapes(); j++)
        {
            int y = SS.Index(tempss.Shape(j));
            if (!graph[i-1][y-1]) graph[i-1][y-1]++;
        }
        tempss.Clear();
    }

}

// graph[i][j] == 1 <=> Shape(i) contains Shape(j)
void BrepToXML::simplify_graph(void)
{
    for (int i = 0; i < SS.NbShapes(); i++) //neglect the fact that an object contains itself
    {
        graph[i][i] = 0;
    }
    for (int i = 0; i < SS.NbShapes(); i++) //for every geometrical object:
    {
        for (int j = i+1; j < SS.NbShapes(); j++) //for every object higher in the hierarchy
        {
            if (graph[j][i]) //if i is contained by j
            {
                for (int k = j+1; k < SS.NbShapes(); k++) //for every k higher than j
                {
                    if((graph[k][j])&&(graph[k][i])) //if j is contained by k and i is contained by k
                    {
                        graph[k][i] = 0; //=> i is contained indirectly by k so we could delete this edge
                    }
                }
            }
        }
    }
}


void BrepToXML::print_graph(void)
{
    cout << SS.NbShapes() << endl;
    for(int i = 0; i < SS.NbShapes(); i++)
    {
        for(int j = 0; j < SS.NbShapes(); j++)
        {
            cout << graph[i][j] << " ";
        }
        cout << endl;
    }
}















void BrepToXML::cacheProperties(const TopoDS_Shape& sh) 
{
    TopoDS_Iterator it(sh);
    for(;it.More();it.Next())
    {
        const TopoDS_Shape& child = it.Value();
        TopAbs_ShapeEnum childType;
        childType = child.ShapeType();
        switch (childType) 
        {
            case TopAbs_COMPOUND:
                break;
            case TopAbs_COMPSOLID:
                break;
            case TopAbs_SOLID:
                break;
            case TopAbs_SHELL:
                break;
            case TopAbs_FACE:
            
                break;
            case TopAbs_WIRE:
                break;
                case TopAbs_SHAPE:
                break;
            case TopAbs_EDGE:
                //TODO extract data describing the curve: 
                //
                //Handle(Geom_Curve) aCurve3d = 
                //BRep_Tool::Curve (anEdge, aFirst, aLast)
                break;
            case TopAbs_VERTEX:
                gp_Pnt vLoc;
                //vertLoc.X(), .Y() and .Z() -- absolute location values on x, y
                // and z axis.
                const TopoDS_Vertex& castChild = TopoDS::Vertex(child);

                vLoc = BRep_Tool::Pnt(castChild);
                pair < int, gp_Pnt > indexedVLoc(SS.Index(child), vLoc);
                vLocs.push_back(indexedVLoc);  
                break;
        }
              
        cacheProperties(child);
    }
}

void BrepToXML::build_xml(void)
{
    
}
