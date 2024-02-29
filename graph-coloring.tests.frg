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

pred cyclic_graph[coloring: Coloring] {
  wellformed
  all vertex: Vertex | {#{adj_vertex: Vertex | adj_vertex in vertex.adjacent} = 2
  is_wellformed_coloring[coloring]
     }
}
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
      //some coloring: Coloring | cyclic_graph[coloring]
      //} for exactly 3 Color, exactly 1 Coloring is theorem}
}
     -- problem:  gives counter example
-- question : why does it give a counter example when we claim *existence* of a coloring. The fact that one coloring doesn't work doesn't refute existencce

test suite for wellformed_and_colored {
    -- no graph can be colored with one color
    test expect { one_color_impossible: {
        wellformed_and_colored
        #{v: Vertex | some v} > 1
    } for exactly 1 Color is unsat}

    test expect {incomplete_color: {
      wellformed_and_colored
      some vertex: Vertex | {no Coloring.color[vertex]}
      } for exactly 1 Coloring is unsat} 

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

pred initial_all {
  all coloring: Coloring | initial[coloring]
}

test suite for initial_all {
  example noColorsInitial is { initial_all } for {
    Vertex = `Vertex1 + `Vertex2
    Coloring = `Coloring0
    no `Coloring0.color
  }

  example oneColorInitial is { not initial_all } for {
    Vertex = `Vertex1 + `Vertex2
    Color = `Red
    Coloring = `Coloring0
    `Coloring0.color = `Vertex1 -> `Red
  }
}

pred fully_colored_all { all coloring: Coloring | fully_colored[coloring] }

test suite for fully_colored_all {
  example noColorsFull is { not fully_colored_all } for {
    Vertex = `Vertex1 + `Vertex2
    Coloring = `Coloring0
    no `Coloring0.color
  }

  example oneColorFull is { fully_colored_all } for {
    Vertex = `Vertex1 + `Vertex2
    Color = `Red
    Coloring = `Coloring0
    `Coloring0.color = `Vertex1 -> `Red + `Vertex2 -> `Red
  }

  example onlyOneVertexFull is { not fully_colored_all } for {
    Vertex = `Vertex1 + `Vertex2
    Color = `Red
    Coloring = `Coloring0
    `Coloring0.color = `Vertex1 -> `Red
  }
}

test suite for coloring_trace {
  // only vertices adjacent to colored vertices can be colored in the next greedy step
  example colorNonAdjacent is { not coloring_trace } for {
    -- graph (a line)
    Vertex = `Vertex1 + `Vertex2 + `Vertex3
    `Vertex1.adjacent = `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2

    -- colors
    Color = `Red + `Blue
    Coloring = `Coloring0 + `Coloring1 + `Coloring2

    no `Coloring0.color
    `Coloring1.color = `Vertex1 -> `Red
    `Coloring2.color = `Vertex1 -> `Red + `Vertex2 -> `Blue + `Vertex3 -> `Red

    Greedy = `Greedy0
    `Greedy0.first = `Coloring0
    `Greedy0.next = `Coloring0 -> `Coloring2 
                  + `Coloring1 -> `Coloring2
  }

  // theorem that at some point there is some instance that is fully colored in the coloring trace
  // coloring_trace terminates with a fully colored graph
  // in conjunction with the inductive verification means that it will always find a coloring or be unsatisfiable
  test expect {fully_colored_in_trace: {
    (wellformed and coloring_trace) implies {
      some coloring: Coloring | {
        (coloring = Greedy.first) or #^(Greedy.next).coloring > 0
        and fully_colored[coloring]
      }
    }
  } for {next is linear} is theorem}

  test expect {cyclic_graph_impossible: {
    some coloring: Coloring | {
      cyclic_graph[coloring]
      coloring_trace
    }
  } for exactly 3 Vertex, exactly 2 Color is unsat}

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

test suite for wellformed_colorings {

  // if there's a valid coloring, then the greedy algorithm will find it
  test expect {greedy_and_existence_equivalence: {
    (wellformed and wellformed_colorings) implies {
      some coloring: Coloring | {
        (coloring = Greedy.first) or #^(Greedy.next).coloring > 0
        fully_colored[coloring]
      }
      wellformed
    }
  } for {next is linear} is theorem}
}



// we want a full coloring of the graph at the very end
// once the graph is colored, colors cannot be "changed"
// graph can be colored via greedy algorithm iff it has a coloring
// if a graph with five vertices can be colored with three colors, it can be colored with four colors
// colorings on cyclic graphs that are constructed (any constructed graphs, for that matter) 
// check that each step only colors adjacent vertices of the already colored vertices
// inductive proof that at each greedy step, if we have new colors, it doesn't violate the overall coloring predicate