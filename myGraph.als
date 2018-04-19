open util/graph[Vertex] as g
open util/integer

sig Vertex {
	edges : set Edge
}

sig Edge {
	source: one Vertex,
	sink : one Vertex,
	weight: Int
}

/** models a connected, undirected graph 
 with no restrictions on cycles **/
pred undirectedGraph (graph: Vertex -> Vertex) {
	undirected[graph]
	weaklyConnected[graph]
	noSelfLoops[graph]
}

/** models symmetric weighted edges on a graph **/
pred weightedEdges (graph: Vertex -> Vertex) {
	-- constrains all edges in graph must directly correspond to vertex relations
	all disj v, v' : Vertex.graph | v->v' in graph implies some e : Edge | e.source = v and e.sink = v' and e in v.edges
	all e : Edge | e.source->e.sink in graph
	--removes any 'duplicate' edges that might have the same source and sink
	all disj e, e' : Edge | e.source = e'.source implies e.sink != e'.sink
	--all edges are unique
	all disj v, v' : Vertex.graph | all e : Edge | e in v.edges implies e not in v'.edges
	--constrains symmetric relation of sink/source and their weights
	all v : Vertex.graph| all e : v.edges | one e' : e.sink.edges |  v = e'.sink and (v = e'.sink implies e'.weight = e.weight)
}

/** models our graph representation **/
pred wellFormedGraph(graph: Vertex -> Vertex) {
	undirectedGraph[graph]
	weightedEdges[graph]
}

/** determines if graph 1 spans graph 2 **/
pred spans(graph1, graph2: Vertex -> Vertex) {
	--subgraph
	graph1 in graph2
	--all nodes covered
	all n : (graph2.Vertex + Vertex.graph2) | n in (graph1.Vertex + graph1.Vertex)
}

<<<<<<< 74b4b4dc8a4de418f28146abc4015c7a657ecbc0
/** determines if graph is an undirected tree **/
pred isUndirectedTree (graph: Vertex -> Vertex) {
	--symmetric
	graph = ~graph
	--connected
	all disj v1, v2: Vertex | v1 in v2.^graph
	--acyclic
	no v : Vertex | (v in v.graph || some v1 : v.graph | let edges1 = graph - (v -> v1) - (v1 -> v) | v1 in v.*edges1)
}

/** produces spanning tree **/
pred isSpanningTree(tree, graph: Vertex->Vertex) {
	isUndirectedTree[tree]
	spans[tree, graph]

}

/** sums the weights of all edges in a graph**/
fun sumWeights(graph: Vertex->Vertex) : Int {
	sum e : ((graph.Vertex).edges)| e.weight
}

/** limit weight size **/
fact smallWeights {
	all e : Edge | e.weight < 10 and e.weight > 0 
	all disj e, e' : Edge | e.weight = e'.weight iff (e.source = e'.sink and e.sink =e'.source)
}

/** determines if tree is an MST of graph 2 **/
pred isMST(tree, graph: Vertex -> Vertex) {
	--well formed graph w weighted edge correspondence
	wellFormedGraph[graph]
	--assert tree is in fact an undirected spanning tree of graph
	isSpanningTree[tree,graph]

	some disj v1, v2 : tree.Vertex | some disj v1', v2' : (graph - (v1->v2) - (v2->v1)).Vertex |
		(v1->v2 in tree) and (v1'->v2' in graph) and (isSpanningTree[(tree-(v1->v2)-(v2->v1)+(v1'->v2')+(v2'->v1')) , graph]
		 	implies (sumWeights[tree+(v1'->v2')+(v2'->v1')-(v1->v2)-(v2->v1)] > sumWeights[tree]))

}

run isMST for exactly 4 Vertex, 10 Edge, 7 Int
=======
/** sums the weights of all edges in the edge set **/
--fun sumWeights(e : set Edge) : Int {
--	sum edge : e | edge.weight
--	all v : graph.Vertex | let total = sum e: v.edges | e.weight
--}

fact smallWeights{
	all e : Edge | e.weight < 10
}

run showGraph for exactly 3 Vertex, 6 Edge, 7 Int
>>>>>>> updating proposal






