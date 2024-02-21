#lang forge

open "graph-coloring.frg"

------------------------------------------------------------------------

test suite for colorings {
    test expect { one_color_impossible: {
        wellformed and colorings
        #{v: Vertex | some v} > 1
    } for exactly 1 Color is unsat}
}