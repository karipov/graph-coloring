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

pred wellformed_partial_coloring {
  all coloring : Coloring | {
    -- all vertices are colored
    all vertex: Vertex | lone coloring.color[vertex]

    -- no two adjacent vertices have the same color
    all disj v1, v2: Vertex | {
      ((some coloring.color[v1] or some coloring.color[v2])
        and v2 in v1.adjacent) implies (coloring.color[v2] != coloring.color[v1])
    }
  }
}

-- initial coloring has no colored vertices
pred initial[coloring: Coloring]{
  all vertex: Vertex | {no coloring.color[vertex]}
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
  wellformed_partial_coloring
}

-- greedy coloring sig: next is linear in time
one sig Greedy {
  first: one Coloring,
  next: pfunc Coloring -> Coloring 
}

-- define coloring trace
pred coloring_trace {
  initial[Greedy.first]
  all coloring: Coloring | {
    some Greedy.next[coloring] implies {
      greedy_step[coloring, Greedy.next[coloring]]
    }
  }
}


// UNCOMMENT TO SEE VISUALIZATION FOR PART 2
// FEEL FREE TO MODIFY THE NUMBER OF VERTICES AND COLORS

// run {
//   wellformed
//   coloring_trace
// } for exactly 3 Vertex, exactly 2 Color for {next is linear}