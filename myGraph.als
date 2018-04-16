open util/graph[Vertex] as g

sig Vertex {
	edges : set Edge
}

sig Edge {
	source: one Vertex,
	sink : one Vertex,
	/* no restriction on negative edge weights, apply nonneg fact for dijkstras */
	weight: Int
}

/** models a connected, undirected graph 
 with no restrictions on cycles **/
pred wellFormedGraph (graph: Vertex -> Vertex) {
	undirected[graph]
	weaklyConnected[graph]
	noSelfLoops[graph]
}

/** models symmetric weighted edges **/
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
pred showGraph(graph: Vertex -> Vertex) {
	wellFormedGraph[graph]
	weightedEdges[graph]
}

/** determines if graph 1 spans graph 2 **/
pred spans(graph1, graph2: Vertex -> Vertex) {
	--subgraph
	graph1 in graph2
	--all nodes covered
	all n : (graph2.Vertex + Vertex.graph2) | n in (graph1.Vertex + graph1.Vertex)
}

/** sums the weights of all edges in the edge set **/
fun sumWeights(e : set Edge) : Int {
	sum edge : e | edge.weight
}

run showGraph for exactly 8 Vertex, 20 Edge






