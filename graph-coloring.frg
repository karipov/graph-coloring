#lang forge

// graph sigs (alternative)
// sig Vertex {
//   color: lone Color
// }

sig Vertex {
  adjacent: set Vertex
}

// sig Edge {
//   from: one Vertex,
//   to: one Vertex
// }

// coloring sigs
abstract sig Color {}
one sig Red, Green, Blue extends Color {}

one sig Coloring {
    color: pfunc Vertex -> Color
}

// define well-formed graphs
// - connected
// - unidrected (if you have to-from then also from-to)
// - no self loops
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

// define well-formed colorings
// - all vertices are colored
// - no two adjacent vertices have the same color
pred colorings {
  -- all vertices are colored
  all vertex: Vertex | one Coloring.color[vertex]

  -- no two adjacent vertices have the same color
  all disj v1, v2: Vertex | {
    v2 in v1.adjacent implies (Coloring.color[v2] != Coloring.color[v1])
  }
}

// question: where do we restrict the number of colors?
run { 
  wellformed
  colorings
} for exactly 3 Vertex//, exactly 3 Color