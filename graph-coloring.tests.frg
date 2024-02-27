#lang forge

open "graph-coloring.frg"

------------------------------------------------------------------------

pred wellformed_and_colored { wellformed and wellformed_colorings }

test suite for wellformed_and_colored {
    -- no graph can be colored with one color
    test expect { one_color_impossible: {
        wellformed_and_colored
        #{v: Vertex | some v} > 1
    } for exactly 1 Color is unsat}

    -- any tree can be colored with two colors
    example fiveVertexTree is { wellformed_and_colored } for {
      Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5
      `Vertex1.adjacent = `Vertex2 + `Vertex3
      `Vertex2.adjacent = `Vertex1 + `Vertex4 + `Vertex5
      `Vertex3.adjacent = `Vertex1

      Color = `Red + `Blue
      Coloring = `Coloring1
      `Coloring1.color =  `Vertex1 -> `Red + 
                          `Vertex2 -> `Blue +
                          `Vertex3 -> `Blue +
                          `Vertex4 -> `Red +
                          `Vertex5 -> `Red
    }
}

-- Inductive verification

pred wellformed_partial_coloring[coloring: Coloring] { --- VALIDATION
  -- all vertices are colored
  all vertex: Vertex | lone coloring.color[vertex]

  -- no two adjacent vertices have the same color
  all disj v1, v2: Vertex | {
    ((some coloring.color[v1] or some coloring.color[v2])
      and v2 in v1.adjacent) implies (coloring.color[v2] != coloring.color[v1])
  }

  wellformed
}

pred move_from_partial_coloring[pre, post: Coloring] {
  wellformed_partial_coloring[pre]
  greedy_step[pre, post]
  wellformed
}

assert all coloring: Coloring | initial[coloring] is sufficient for wellformed_partial_coloring[coloring]
assert all pre, post: Coloring | move_from_partial_coloring[pre, post] is sufficient for wellformed_partial_coloring[post]



// we want a full coloring of the graph at the very end
// once the graph is colored, colors cannot be "changed"
// graph can be colored via greedy algorithm iff it has a coloring
// if a graph with five vertices can be colored with three colors, it can be colored with four colors
// colorings on cyclic graphs that are constructed (any constructed graphs, for that matter) 
// check that each step only colors adjacent vertices of the already colored vertices
// inductive proof that at each greedy step, if we have new colors, it doesn't violate the overall coloring predicate