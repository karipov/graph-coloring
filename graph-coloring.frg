#lang forge

// graph
sig Vertex {
  adjacent: set Vertex
}

// coloring sigs
sig Color {}
// one sig Red, Green, Blue extends Color {}

one sig Coloring {
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
  all v: Vertex | not v in v.adjacent
}

// all graphs are colored correctly
pred colorings {
  -- all vertices are colored
  all vertex: Vertex | one Coloring.color[vertex]

  -- no two adjacent vertices have the same color
  all disj v1, v2: Vertex | {
    v2 in v1.adjacent implies (Coloring.color[v2] != Coloring.color[v1])
  }
}

pred tree {
  // characterize a tree by having no cycles
  all vertex : Vertex | {
    not reachable[vertex, vertex, adjacent]
  }
}

run { 
  wellformed
  colorings
} for exactly 3 Vertex