#lang forge

// graph
sig Vertex {
  adjacent: set Vertex
}

// coloring sigs
sig Color {}
// one sig Red, Green, Blue extends Color {}

sig Coloring {
    color: pfunc Vertex -> Color
}

// all graphs are well-formed
pred wellformed {
  all disj v1, v2: Vertex | {
    -- connected
    reachable[v1, v2, adjacent] 

    -- undirected
    v1 in v2.adjacent implies v2 in v1.adjacent
  }

  -- no self loops
    all v: Vertex | {not v in v.adjacent}
}

// all graphs are colored correctly
pred wellformed_colorings {
  -- all vertices are colored
  all coloring : Coloring | {
    all vertex: Vertex | one Coloring.color[vertex]

  -- no two adjacent vertices have the same color
    all disj v1, v2: Vertex | {
      v2 in v1.adjacent implies (Coloring.color[v2] != Coloring.color[v1])
  }
  }
}

pred tree {
  // a tree is connected
  some init_vertex: Vertex | {
    all other_vertex: Vertex | {
      reachable[other_vertex, init_vertex, adjacent]
    }
  }
  
  // characterize a tree by having no cycles
  all v: Vertex | (not v in v.adjacent) and (not reachable[v,v,adjacent])
}

run { 
  wellformed
  wellformed_colorings
} for exactly 3 Vertex

pred wellformed_partial_coloring {
  -- all vertices are colored
  all coloring : Coloring | {
    all vertex: Vertex | lone Coloring.color[vertex]

  -- no two adjacent vertices have the same color
    all disj v1, v2: Vertex | {
      v2 in v1.adjacent implies (Coloring.color[v2] != Coloring.color[v1])
    }
  }
}

pred initial[coloring: Coloring]{
  all vertex: Vertex | {no coloring.color[vertex]}
}

pred greedy_step[pre: Coloring, post: Coloring] {
  -- if pre has no colored vertices, then post has exactly one colored vertex
  initial[pre] implies {one vertex: Vertex | {some post.color[vertex]}}
  -- if pre has colored vertices, then all of the adjecent vertices of the colored vertices in pre are colored in post
  all vertex1, vertex2: Vertex | {
    (vertex2 in vertex1.adjacent and some pre.color[vertex1]) implies some post.color[vertex2]
    }
  -- all the colored vertices in pre have the same color in post
  all vertex : Vertex | {some pre.color[vertex] implies pre.color[vertex] = post.color[vertex]}
  -- the partial colorings are wellformed
  wellformed_partial_coloring
}

one sig Greedy {
  first: one Coloring,
  next: pfunc Coloring -> Coloring 
}

pred coloring_trace {
  initial[Greedy.first]
  all coloring: Coloring | {
    some Greedy.next[coloring] implies {
      some next_coloring: Coloring | {
        greedy_step[coloring, next_coloring]
      }
    }
  }
}