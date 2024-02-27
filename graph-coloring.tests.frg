#lang forge

open "graph-coloring.frg"

------------------------------------------------------------------------
test suite for wellformed {
  example directed is {not wellformed} for {
    Vertex = `Vertex1 + `Vertex2
    `Vertex1.adjacent = `Vertex2
  }

  example unconnected is {not wellformed} for {
    Vertex = `Vertex1 + `Vertex2
  }

  example selfLoop is {not wellformed} for {
    Vertex = `Vertex1
    `Vertex1.adjacent = `Vertex1
  }

  example cyclic is {wellformed} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5
    `Vertex1.adjacent = `Vertex5 + `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex4
    `Vertex4.adjacent = `Vertex3 + `Vertex5
    `Vertex5.adjacent = `Vertex4 + `Vertex1
  }

  example SixVertexTree is {wellformed} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5 + `Vertex6
    `Vertex1.adjacent = `Vertex2 + `Vertex3 + `Vertex6
    `Vertex2.adjacent = `Vertex1 + `Vertex4 + `Vertex5
    `Vertex3.adjacent = `Vertex1
    `Vertex4.adjacent = `Vertex2
    `Vertex5.adjacent = `Vertex2
    `Vertex6.adjacent = `Vertex1
  }

  example ThreeClique is {wellformed} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 
    `Vertex1.adjacent = `Vertex2 + `Vertex3
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex1
  }
}

pred wellformed_and_colored { wellformed and wellformed_colorings }

pred cyclic_graph{wellformed and (all vertex: Vertex | { #{adj_vertex: Vertex | adj_vertex in vertex.adjacent} = 2})}
//assert cyclic_graph is sufficient for wellformed_colorings for exactly 3 Color

pred is_wellformed_coloring[coloring: Coloring] {
    all vertex: Vertex | one coloring.color[vertex]
    all disj v1, v2: Vertex | {
      v2 in v1.adjacent implies (coloring.color[v2] != coloring.color[v1])
    }
}

test suite for is_wellformed_coloring {
-- as soon as a graph is cyclic it can be colored with three colors
    //test expect {cyclic_graph_three_colored: {
    //  cyclic_graph implies {some coloring: Coloring | is_wellformed_coloring[coloring]}
    //} for exactly 3 Color, exactly 1 Coloring is theorem}
} -- problem:  gives counter example
-- question : why does it give a counter example when we claim *existence* of a coloring. The fact that one coloring doesn't work doesn't refute existencce

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
      `Vertex4.adjacent = `Vertex2
      `Vertex5.adjacent = `Vertex2

      Color = `Red + `Blue
      Coloring = `Coloring1
      `Coloring1.color =  `Vertex1 -> `Red + 
                          `Vertex2 -> `Blue +
                          `Vertex3 -> `Blue +
                          `Vertex4 -> `Red +
                          `Vertex5 -> `Red
    }

  -- a clique with N vertices cannot be colored with N-1 colors
  example ThreeCliqueTwoColors is {not wellformed_and_colored} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 
    `Vertex1.adjacent = `Vertex2 + `Vertex3
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex1

    Color = `Red + `Blue
    Coloring = `Coloring1
    `Coloring1.color =  `Vertex1 -> `Red + 
                        `Vertex2 -> `Blue +
                        `Vertex3 -> `Blue
  }
    
  -- a clique with N vertices can be colored with N colors
  example ThreeCliqueThreeColors is {wellformed_and_colored} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 
    `Vertex1.adjacent = `Vertex2 + `Vertex3
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex1

    Color = `Red + `Blue + `Green
    Coloring = `Coloring1
    `Coloring1.color =  `Vertex1 -> `Red + 
                        `Vertex2 -> `Blue +
                        `Vertex3 -> `Green
  }

  -- cyclic graphs with an even number of vertices can be colored with 2 colors
  example cyclicEvenTwoColors is {wellformed_and_colored} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5 + `Vertex6
    `Vertex1.adjacent = `Vertex6 + `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex4
    `Vertex4.adjacent = `Vertex3 + `Vertex5
    `Vertex5.adjacent = `Vertex4 + `Vertex6
    `Vertex6.adjacent = `Vertex5 + `Vertex1

    Color = `Red + `Blue
    Coloring = `Coloring1
    `Coloring1.color =  `Vertex1 -> `Red + 
                        `Vertex2 -> `Blue +
                        `Vertex3 -> `Red +
                        `Vertex4 -> `Blue +
                        `Vertex5 -> `Red +
                        `Vertex6 -> `Blue 
  }
  
  -- a coloring with a non minimal number of colors is still wellformed
  example unoptimal is {wellformed_and_colored} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5 + `Vertex6
    `Vertex1.adjacent = `Vertex6 + `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex4
    `Vertex4.adjacent = `Vertex3 + `Vertex5
    `Vertex5.adjacent = `Vertex4 + `Vertex6
    `Vertex6.adjacent = `Vertex5 + `Vertex1

    Color = `Red + `Blue + `Green
    Coloring = `Coloring1
    `Coloring1.color =  `Vertex1 -> `Red + 
                        `Vertex2 -> `Blue +
                        `Vertex3 -> `Red +
                        `Vertex4 -> `Green +
                        `Vertex5 -> `Red +
                        `Vertex6 -> `Blue
  }
}

-- Inductive verification that a step in the greedy algorithm preserves wellformed colorings

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