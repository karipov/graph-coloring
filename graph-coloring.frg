#lang forge

// -------------------------------- GENERAL SIGS -------------------------------------

sig Vertex {
  adjacent: set Vertex
}

sig Color {}

sig Coloring {
    color: pfunc Vertex -> Color
}

// ------------------------ PART 1: GRAPH COLORING EXISTENCE -------------------------

// all graphs are well-formed
pred wellformed {
  all disj v1, v2: Vertex | {
    -- connected
    reachable[v1, v2, adjacent] 

    -- undirected
    v1 in v2.adjacent implies v2 in v1.adjacent
  }

  -- no self loops
  all v: Vertex | {not v in v.adjacent}
}

// all graphs are colored correctly
pred wellformed_colorings {
  -- all vertices are colored
  all coloring : Coloring | {
    all vertex: Vertex | one coloring.color[vertex]

  -- no two adjacent vertices have the same color
    all disj v1, v2: Vertex | {
      v2 in v1.adjacent implies (coloring.color[v2] != coloring.color[v1])
    }
  }
}

// UNCOMMENT TO SEE VISUALIZATION FOR PART 1
// FEEL FREE TO MODIFY THE NUMBER OF VERTICES AND COLORS

// run { 
//   wellformed
//   wellformed_colorings
// } for exactly 3 Vertex, exactly 2 Color, exactly 1 Coloring


// -------------------------- PART 2: GREEDY GRAPH COLORING --------------------------

-- initial coloring has no colored vertices
pred initial[coloring: Coloring]{
  wellformed
  all vertex: Vertex | {no coloring.color[vertex]}
}

-- ensure that the new colored vertices don't clash with previous colorings
pred coloring_invariant[pre, post: Coloring] {
  all vertex: Vertex | {
    (no pre.color[vertex] and some post.color[vertex]) implies
      #{ other_vertex: Vertex |
        (other_vertex in vertex.adjacent)
          and (post.color[vertex] = post.color[other_vertex]) } = 0
  }
}

-- checking if coloring is completed
pred fully_colored[coloring: Coloring] {
  all vertex: Vertex | {some coloring.color[vertex]}
}

-- define the greedy coloring step
pred greedy_step[pre: Coloring, post: Coloring] {
  -- if pre has no colored vertices, then post has exactly one colored vertex
  initial[pre] implies {one vertex: Vertex | {some post.color[vertex]}}

  -- if pre has colored vertices, then all of the adjacent vertices of the colored
  -- vertices in pre are colored in post
  all vertex1, vertex2: Vertex | {
    (vertex2 in vertex1.adjacent
      and some pre.color[vertex1]) implies some post.color[vertex2]
  }

  -- if no colored neighbors in pre, then vertex not colored in post
  (not initial[pre]) implies { 
    all v1: Vertex | {
        (#{v: Vertex | v in v1.adjacent and some pre.color[v]} = 0
          and no pre.color[v1]) implies no post.color[v1]
    }
  }

  -- all the colored vertices in pre have the same color in post
  all vertex : Vertex | {
    some pre.color[vertex] implies pre.color[vertex] = post.color[vertex]
  }

  -- the partial colorings are wellformed
  -- wellformed_partial_coloring
  coloring_invariant[pre, post]

  -- prevent fully colored graphs from progressing
  not fully_colored[pre]
}

-- greedy coloring sig: next is linear in time
one sig Greedy {
  first: one Coloring,
  next: pfunc Coloring -> Coloring 
}

-- define coloring trace
pred coloring_trace {
  -- initial state has no coloring
  initial[Greedy.first]

  -- all colorings follow the greedy step
  all coloring: Coloring | {
    some Greedy.next[coloring] implies {
      greedy_step[coloring, Greedy.next[coloring]]
    }
  }

  -- make sure that there is some end state that is fully colored
  some other_coloring: Coloring | {
    fully_colored[Greedy.next[other_coloring]]
  }
}


// UNCOMMENT TO SEE VISUALIZATION FOR PART 2
// FEEL FREE TO MODIFY THE NUMBER OF VERTICES AND COLORS

run {
  wellformed
  coloring_trace
} for exactly 3 Vertex, exactly 2 Color, 4 Coloring for {next is linear}