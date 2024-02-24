#lang forge

open "graph-coloring.frg"

------------------------------------------------------------------------

test suite for colorings {
    test expect { one_color_impossible: {
        wellformed and colorings
        #{v: Vertex | some v} > 1
    } for exactly 1 Color is unsat}

    test expect {two_color_tree: {
        tree and colorings
         #{v: Vertex | some v} > 1
    } for exactly 2 Color is sat}

    // write a test saying that tree is sufficient for having a sat coloring with two colors
    assert tree is sufficient for colorings for exactly 2 Color
}