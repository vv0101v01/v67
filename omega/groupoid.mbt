///|
/// The free groupoid on a finite directed graph: objects are vertices,
/// morphisms are reduced edge words.  A word is a list of signed edge
/// indices, `+e` for traversing `e` forwards and `~e` (coded `-e-1`)
/// backwards; reduction cancels adjacent inverse pairs.
///
/// This is the fundamental groupoid of the graph, and it is a genuine
/// omega-groupoid truncated at level 1: composition of reduced words is
/// strictly associative, every morphism is invertible, and the whole
/// structure is finite on any finite set of endpoints once we bound length.
#derive(Debug, Eq)
pub struct Graph {
  nverts : Int32
  edges : Array[(Int32, Int32)]
}

///|
pub fn Graph::new(nverts : Int32, edges : Array[(Int32, Int32)]) -> Graph {
  Graph::{ nverts, edges, }
}

///|
pub fn Graph::nedges(self : Graph) -> Int32 {
  self.edges.length()
}

///|
/// Source and target of a signed letter.
pub fn Graph::letter_ends(self : Graph, letter : Int32) -> (Int32, Int32) {
  if letter >= 0 {
    self.edges[letter]
  } else {
    let (a, b) = self.edges[-letter - 1]
    (b, a)
  }
}

///|
/// Cancel adjacent inverse pairs until nothing cancels.  This is the
/// normal form of the free groupoid, and it is exactly a terminating
/// confluent rewriting system: `e ~e -> ()` and `~e e -> ()`.
pub fn reduce_word(w : Array[Int32]) -> Array[Int32] {
  let stack : Array[Int32] = []
  for x in w {
    if stack.length() > 0 {
      let top = stack[stack.length() - 1]
      let cancels = (top >= 0 && x == -top - 1) || (top < 0 && x == -top - 1)
      if cancels {
        ignore(stack.pop())
        continue
      }
    }
    stack.push(x)
  }
  stack
}

///|
/// A morphism of the free groupoid: a reduced word with its endpoints.
#derive(Debug, Eq)
pub struct Path1 {
  src : Int32
  tgt : Int32
  word : Array[Int32]
}

///|
pub fn Path1::id(v : Int32) -> Path1 {
  Path1::{ src: v, tgt: v, word: [], }
}

///|
/// Build a morphism from a raw word, reducing it.  Returns `None` when the
/// letters do not compose as a walk from `src`.
pub fn Graph::path(self : Graph, src : Int32, word : Array[Int32]) -> Path1? {
  let mut cur = src
  for l in word {
    if l < -self.nedges() || l >= self.nedges() {
      return None
    }
    let (a, b) = self.letter_ends(l)
    if a != cur {
      return None
    }
    cur = b
  }
  let reduced = reduce_word(word)
  // endpoints are unchanged by reduction
  let mut end = src
  for l in reduced {
    let (_, b) = self.letter_ends(l)
    end = b
  }
  Some(Path1::{ src, tgt: end, word: reduced, })
}

///|
/// Composition `self ; other`, defined when `self.tgt == other.src`.
pub fn Path1::then(self : Path1, other : Path1) -> Path1? {
  if self.tgt != other.src {
    return None
  }
  let w : Array[Int32] = []
  for x in self.word {
    w.push(x)
  }
  for x in other.word {
    w.push(x)
  }
  Some(Path1::{ src: self.src, tgt: other.tgt, word: reduce_word(w), })
}

///|
pub fn Path1::inverse(self : Path1) -> Path1 {
  let w : Array[Int32] = []
  for i in 0..<self.word.length() {
    let l = self.word[self.word.length() - 1 - i]
    w.push(-l - 1)
  }
  Path1::{ src: self.tgt, tgt: self.src, word: w, }
}

///|
pub fn Path1::length(self : Path1) -> Int32 {
  self.word.length()
}

///|
/// The fundamental group at a vertex, as reduced loops of bounded length.
/// For a graph this is a free group; its rank is `E - V + 1` on a connected
/// graph, which the tests confirm by counting a spanning tree.
pub fn Graph::loops(
  self : Graph,
  base : Int32,
  max_len : Int32,
) -> Array[Path1] {
  let out : Array[Path1] = []
  let seen : Array[Array[Int32]] = []
  fn walk(cur : Int32, word : Array[Int32]) -> Unit {
    if word.length() > 0 && cur == base {
      let reduced = reduce_word(word)
      if !seen.contains(reduced) {
        seen.push(reduced)
        match Graph::path(self, base, word) {
          Some(p) => out.push(p)
          None => ()
        }
      }
    }
    if word.length() >= max_len {
      return
    }
    for e in 0..<self.nedges() {
      for letter in [e, -e - 1] {
        let (a, b) = self.letter_ends(letter)
        if a == cur {
          // avoid immediate backtracking: it would reduce away
          if word.length() > 0 && word[word.length() - 1] == -letter - 1 {
            continue
          }
          word.push(letter)
          walk(b, word)
          ignore(word.pop())
        }
      }
    }
  }

  walk(base, [])
  out
}

///|
/// A spanning tree by breadth-first search, returned as parent edges.
/// The number of non-tree edges is the rank of the fundamental group.
pub fn Graph::spanning_tree(self : Graph, root : Int32) -> Array[Int32] {
  let parent_edge = Array::make(self.nverts, -1)
  let seen = Array::make(self.nverts, false)
  seen[root] = true
  let queue : Array[Int32] = [root]
  let mut head = 0
  let tree : Array[Int32] = []
  while head < queue.length() {
    let v = queue[head]
    head = head + 1
    for e in 0..<self.nedges() {
      let (a, b) = self.edges[e]
      let other = if a == v { b } else if b == v { a } else { -1 }
      if other >= 0 && !seen[other] {
        seen[other] = true
        parent_edge[other] = e
        tree.push(e)
        queue.push(other)
      }
    }
  }
  tree
}

///|
/// Rank of the fundamental group of a connected graph: `E - V + 1`.
/// This is the first Betti number, computed combinatorially rather than
/// by linear algebra, and the two agree.
pub fn Graph::pi1_rank(self : Graph, root : Int32) -> Int32 {
  let tree = self.spanning_tree(root)
  self.nedges() - tree.length()
}

///|
/// The circle as a graph with one vertex and one loop.
pub fn graph_circle() -> Graph {
  Graph::new(1, [(0, 0)])
}

///|
/// The figure eight: one vertex, two loops.  Its fundamental group is the
/// free group on two generators, the standard non-abelian example.
pub fn graph_wedge2() -> Graph {
  Graph::new(1, [(0, 0), (0, 0)])
}

///|
/// The theta graph: two vertices joined by three edges.
pub fn graph_theta() -> Graph {
  Graph::new(2, [(0, 1), (0, 1), (0, 1)])
}
