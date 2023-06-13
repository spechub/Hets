from ogdf_python import ogdf, cppinclude
cppinclude("ogdf/basic/graph_generators/randomized.h")
cppinclude("ogdf/layered/SugiyamaLayout.h")

G = ogdf.Graph()
ogdf.setSeed(1)
ogdf.randomPlanarTriconnectedGraph(G, 20, 40)
GA = ogdf.GraphAttributes(G, ogdf.GraphAttributes.all)

for n in G.nodes:
    GA.label[n] = "N%s" % n.index()

SL = ogdf.SugiyamaLayout()
SL.call(GA)
GA
