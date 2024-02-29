#lang forge

open "graph-coloring.frg"

-------------------------------------------------------------------------------------

// predicates that will be used in our testing

pred wellformed_and_colored { wellformed and wellformed_colorings }

-- defining a cyclix graph
pred cyclic_graph[coloring: Coloring] {
  wellformed
  all vertex: Vertex | {#{adj_vertex: Vertex | adj_vertex in vertex.adjacent} = 2
  is_wellformed_coloring[coloring]
     }
}
 -- checks whether an inputted coloring is wellformed
pred is_wellformed_coloring[coloring: Coloring] {
    all vertex: Vertex | one coloring.color[vertex]
    all disj v1, v2: Vertex | {
      v2 in v1.adjacent implies (coloring.color[v2] != coloring.color[v1])
    }
}

-- check whether an inputted coloring colors all the vertices
pred fully_colored_all { all coloring: Coloring | fully_colored[coloring] }

// In this test suite, we chose to present the nice results first and leave the
// over and under constraint checks at the end of the file.

// Inductive verification that a step in the greedy algorithm preserves wellformed colorings

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
  -- define a move from a wellformed partially colored coloring in a wellformed graph
  wellformed_partial_coloring[pre]
  greedy_step[pre, post]
  wellformed
}

-- base case: check that initial colorings are wellformed 
assert all coloring: Coloring | {
  initial[coloring] is sufficient for wellformed_partial_coloring[coloring]
}
-- inductive step: check that if the greedy algorithm makes a step from a wellformed
-- partial coloring, then the resulting coloring will also be wellformed
assert all pre, post: Coloring | {
  move_from_partial_coloring[pre, post] is sufficient for wellformed_partial_coloring[post]
}

// Testing the trace of our Greedy algoritm. We start by testing the basic properties
// and move on to proving a couple of interesting facts.

test suite for coloring_trace {
  -- only vertices adjacent to colored vertices can be colored in the next greedy step
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
    `Greedy0.next = `Coloring0 -> `Coloring1
                  + `Coloring1 -> `Coloring2
  }

  example correct_coloring_trace is { coloring_trace } for {
    -- graph (a line)
    Vertex = `Vertex1 + `Vertex2 + `Vertex3
    `Vertex1.adjacent = `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2

    -- colors
    Color = `Red + `Blue
    Coloring = `Coloring0 + `Coloring1 + `Coloring2 + `Coloring3

    no `Coloring0.color
    `Coloring1.color = `Vertex1 -> `Red
    `Coloring2.color = `Vertex1 -> `Red + `Vertex2 -> `Blue 
    `Coloring3.color = `Vertex1 -> `Red + `Vertex2 -> `Blue + `Vertex3 -> `Red

    Greedy = `Greedy0
    `Greedy0.first = `Coloring0
    `Greedy0.next = `Coloring0 -> `Coloring1
                  + `Coloring1 -> `Coloring2
                  + `Coloring2 -> `Coloring3
  }

-- the coloring algorithm stops once it finds a wellformed coloring
  example doesnt_terminate is { not coloring_trace } for {
    -- graph (a line)
    Vertex = `Vertex1 + `Vertex2 + `Vertex3
    `Vertex1.adjacent = `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2

    -- colors
    Color = `Red + `Blue
    Coloring = `Coloring0 + `Coloring1 + `Coloring2 + `Coloring3 + `Coloring4

    no `Coloring0.color
    `Coloring1.color = `Vertex1 -> `Red
    `Coloring2.color = `Vertex1 -> `Red + `Vertex2 -> `Blue 
    `Coloring3.color = `Vertex1 -> `Red + `Vertex2 -> `Blue + `Vertex3 -> `Red
    `Coloring4.color = `Vertex1 -> `Red + `Vertex2 -> `Blue + `Vertex3 -> `Red

    Greedy = `Greedy0
    `Greedy0.first = `Coloring0
    `Greedy0.next = `Coloring0 -> `Coloring1
                  + `Coloring1 -> `Coloring2
                  + `Coloring2 -> `Coloring3
                  + `Coloring3 -> `Coloring4
  }

  // Theorem that coloring_trace terminates with a fully colored graph.
  // In conjunction with the inductive verification means that it will always find
  // a well-formed coloring or be unsatisfiable 
  test expect {fully_colored_in_trace: {
    -- if the graph is wellformed and there is a coloring trace
    (wellformed and coloring_trace) implies {
      -- then at some point in the coloring trace, there will be a completely colored graph
      some coloring: Coloring | {
        (coloring = Greedy.first) or #^(Greedy.next).coloring > 0
        and fully_colored[coloring]
      }
    }
  } for {next is linear} is theorem}

  -- cylic graphs with three vertices can't be colored with two colors
  test expect {cyclic_graph_impossible: {
    some coloring: Coloring | {
      cyclic_graph[coloring]
      coloring_trace
    }
  } for exactly 3 Vertex, exactly 2 Color is unsat}

  // cyclic graphs can always be colored with three colors
  test expect {cyclic_graph_three_colored: {
    some coloring: Coloring | {
      cyclic_graph[coloring]
      coloring_trace
    }
  } for exactly 3 Color is sat}

}

// The last result of note of this project:
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

  // This, in conjunction with our inductive verification that the Greedy algorithm only finds
  // wellformed colorings implies that a wellformed graph admits a wellformed coloring
  // IF AND ONLY IF the greedy algorithm can find it! This is a pretty strong result :)
}

// Checks that our basic predicates don't over or under constrain 

test suite for wellformed {

  // wellformed graphs are not directed
  example directed is {not wellformed} for {
    Vertex = `Vertex1 + `Vertex2
    `Vertex1.adjacent = `Vertex2
  }

  // wellformed graphs are not disconnected
  example unconnected is {not wellformed} for {
    Vertex = `Vertex1 + `Vertex2
  }

  // wellformed graphs don't contain self loops
  example selfLoop is {not wellformed} for {
    Vertex = `Vertex1
    `Vertex1.adjacent = `Vertex1
  }

  // cyclic graphs are an example of wellformed graphs
  example cyclic is {wellformed} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5
    `Vertex1.adjacent = `Vertex5 + `Vertex2
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex4
    `Vertex4.adjacent = `Vertex3 + `Vertex5
    `Vertex5.adjacent = `Vertex4 + `Vertex1
  }

  //trees are examples of wellformed graphs
  example SixVertexTree is {wellformed} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 + `Vertex4 + `Vertex5 + `Vertex6
    `Vertex1.adjacent = `Vertex2 + `Vertex3 + `Vertex6
    `Vertex2.adjacent = `Vertex1 + `Vertex4 + `Vertex5
    `Vertex3.adjacent = `Vertex1
    `Vertex4.adjacent = `Vertex2
    `Vertex5.adjacent = `Vertex2
    `Vertex6.adjacent = `Vertex1
  }

  // cliques are examples of wellformed graphs
  example ThreeClique is {wellformed} for {
    Vertex = `Vertex1 + `Vertex2 + `Vertex3 
    `Vertex1.adjacent = `Vertex2 + `Vertex3
    `Vertex2.adjacent = `Vertex1 + `Vertex3
    `Vertex3.adjacent = `Vertex2 + `Vertex1
  }
}

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

// testing our fully_colored predicate
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