#lang forge/bsl

// graph sigs
sig Vertex {}

sig Edge {
  from: one Vertex,
  to: one Vertex
}

// coloring sigs
sig Color {}
one sig Red, Green, Blue extends Color {}

sig Coloring { // TODO: ask in office hours
    color: pfunc Vertex -> Color
}

// define well-formed graphs
// - connected
// - unidrected (if you have to-from then also from-to)

// define well-formed colorings
// - all vertices are colored
// - no two adjacent vertices have the same color

// question: where do we restrict the number of colors?
// run {  } for 3 Color