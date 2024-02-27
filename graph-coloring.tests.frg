#lang forge

open "graph-coloring.frg"

------------------------------------------------------------------------

test suite for colorings {
    test expect { one_color_impossible: {
        wellformed and wellformed_colorings
        #{v: Vertex | some v} > 1
    } for exactly 1 Color is unsat}

    test expect {two_color_tree: {
        tree and wellformed_colorings
         #{v: Vertex | some v} > 1
    } for exactly 2 Color is sat}

    // write a test saying that tree is sufficient for having a sat coloring with two colors
    // assert tree is sufficient for colorings for exactly 2 Color
}

// we want a full coloring of the graph at the very end
// once the graph is colored, colors cannot be "changed"
// graph can be colored via greedy algorithm iff it has a coloring
// if a graph with five vertices can be colored with three colors, it can be colored with four colors
// colorings on cyclic graphs that are constructed (any constructed graphs, for that matter) 
// check that each step only colors adjacent vertices of the already colored vertices
// inductive proof that at each greedy step, if we have new colors, it doesn't violate the overall coloring predicate