open util/ordering[State]
open myGraph
open util/integer

sig State {
	unexaminedEdges : set Edge, --unexamined edges
	mst : set Edge, --edges of mst
	graph: Vertex -> Vertex --graph we are working on
}

abstract sig Event {
    pre, post: State,
    e: Edge -- the chosen edge for an iteration
}

sig addEdge extends Event { } {
	--graph does not change over states
	pre.graph = post.graph

	some edge : getMinEdge[pre.unexaminedEdges] | {
		inSameCloud[edge, pre] implies {
			post.mst = pre.mst
			
		} else {
			post.mst = pre.mst + edge
		}
		
		post.unexaminedEdges = pre.unexaminedEdges - edge	

	}
}

fact initialState {
	wellFormedGraph[first.graph]
	(first.mst).isEmpty
	first.unexaminedEdges = graph.Vertex.edges
}


fact endState {
	(last.unexaminedEdges).isEmpty
	--num vertices in mst is same as num vertices in graph
}


fact trace {
	all s: State - last |
		some e: Event | e.pre = s and e.post = s.next
}

pred inSameCloud(edge : Edge, state : State) {
--edge.source in (edge.sink).^(state.formGraphFromEdges[mst]) and edge.sink in (edge.source).^(state.formGraphFromEdges[mst])
--no path from u to v via edges in mst
}

--produce graph from set of edges
fun formGraphFromEdges(edges : set Edge) : Vertex->Vertex {
	--TODO: this must be a unary set, instead it is type Vertex->Vertex
	{graph : Vertex -> Vertex | all e : edges | e.source->e.sink in graph}

}

fun getMinEdge(edges : set Edge) : Edge {
	{e : edges | no e' : edges | lt[e'.weight, e.weight]}
}

run {}
