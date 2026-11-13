///|
/// **The homotopy type of the little cubes spaces, computed finitely.**
///
/// `C_n(k)` is homotopy equivalent to the ordered configuration space of
/// `k` distinct points in `R^n`.  Its set of connected components is
/// therefore `π₀(Conf_k(R^n))`: `k!` for `n = 1` (the order of the points
/// on a line cannot change) and a single point for `n ≥ 2` (there is room
/// to move around).  This is the precise sense in which `E_1` is
/// associative-but-not-commutative while `E_2` is commutative up to
/// homotopy, and it is what the Eckmann–Hilton argument exploits.
///
/// The finite model: `k` labelled tokens on distinct cells of a
/// `grid^n` board, with a move sliding one token to an adjacent free
/// cell.  Such a slide is a path in `C_n(k)`, and for a fine enough grid
/// the components of this graph are exactly `π₀`.  Everything is a finite
/// breadth-first search.
#derive(Debug, Eq)
pub struct Tokens {
  dim : Int32
  grid : Int32
  pos : Array[Int32]
}

///|
pub fn Tokens::new(dim : Int32, grid : Int32, pos : Array[Int32]) -> Tokens {
  Tokens::{ dim, grid, pos, }
}

///|
fn cells_of(dim : Int32, grid : Int32) -> Int32 {
  let mut c = 1
  for _ in 0..<dim {
    c = c * grid
  }
  c
}

///|
/// The coordinates of a cell index, axis 0 least significant.
fn cell_coords(cell : Int32, dim : Int32, grid : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut c = cell
  for _ in 0..<dim {
    out.push(c % grid)
    c = c / grid
  }
  out
}

///|
fn cell_index(coords : Array[Int32], grid : Int32) -> Int32 {
  let mut idx = 0
  let mut mul = 1
  for c in coords {
    idx = idx + c * mul
    mul = mul * grid
  }
  idx
}

///|
/// Encode a token placement as a single integer, so the search can use an
/// integer-keyed map.
fn encode(pos : Array[Int32], cells : Int32) -> Int32 {
  let mut code = 0
  for p in pos {
    code = code * cells + p
  }
  code
}

///|
/// The neighbours of a placement: slide one token by one step along one
/// axis into a free cell.
fn neighbours(t : Tokens) -> Array[Int32] {
  let cells = cells_of(t.dim, t.grid)
  let out : Array[Int32] = []
  for i in 0..<t.pos.length() {
    let coords = cell_coords(t.pos[i], t.dim, t.grid)
    for d in 0..<t.dim {
      for step in [-1, 1] {
        let v = coords[d] + step
        if v < 0 || v >= t.grid {
          continue
        }
        let nc = coords[:].to_owned()
        nc[d] = v
        let target = cell_index(nc, t.grid)
        let mut free = true
        for j in 0..<t.pos.length() {
          if j != i && t.pos[j] == target {
            free = false
          }
        }
        if free {
          let np = t.pos[:].to_owned()
          np[i] = target
          out.push(encode(np, cells))
        }
      }
    }
  }
  out
}

///|
/// All placements of `k` labelled tokens on distinct cells.
fn all_placements(dim : Int32, grid : Int32, k : Int32) -> Array[Int32] {
  let cells = cells_of(dim, grid)
  let out : Array[Int32] = []
  let cur : Array[Int32] = []
  fn go(depth : Int32) -> Unit {
    if depth == k {
      out.push(encode(cur, cells))
      return
    }
    for c in 0..<cells {
      let mut free = true
      for p in cur {
        if p == c {
          free = false
        }
      }
      if free {
        cur.push(c)
        go(depth + 1)
        ignore(cur.pop())
      }
    }
  }

  go(0)
  out
}

///|
fn decode(code : Int32, cells : Int32, k : Int32) -> Array[Int32] {
  let out = Array::make(k, 0)
  let mut c = code
  for i in 0..<k {
    out[k - 1 - i] = c % cells
    c = c / cells
  }
  out
}

///|
/// The connected components of the discretised `C_n(k)`, as a sorted list
/// of component sizes.  The number of components is `π₀`.
pub fn config_components(dim : Int32, grid : Int32, k : Int32) -> Array[Int32] {
  let cells = cells_of(dim, grid)
  let states = all_placements(dim, grid, k)
  let index : Map[Int32, Int32] = Map([])
  for i in 0..<states.length() {
    index[states[i]] = i
  }
  let seen = Array::make(states.length(), false)
  let sizes : Array[Int32] = []
  for start in 0..<states.length() {
    if seen[start] {
      continue
    }
    seen[start] = true
    let queue : Array[Int32] = [states[start]]
    let mut head = 0
    let mut size = 0
    while head < queue.length() {
      let code = queue[head]
      head = head + 1
      size = size + 1
      let t = Tokens::new(dim, grid, decode(code, cells, k))
      for nb in neighbours(t) {
        match index.get(nb) {
          Some(j) =>
            if !seen[j] {
              seen[j] = true
              queue.push(nb)
            }
          None => ()
        }
      }
    }
    sizes.push(size)
  }
  sizes.sort()
  sizes
}

///|
/// `π₀(C_n(k))` as computed by the finite model.
pub fn pi0_config(dim : Int32, grid : Int32, k : Int32) -> Int32 {
  config_components(dim, grid, k).length()
}

///|
/// Can the first two tokens be exchanged by a motion of the
/// configuration?  For `n = 1` never, for `n ≥ 2` always (on a fine
/// enough grid).  This is the failure / success of commutativity for the
/// binary operation of `E_n`, decided by reachability.
pub fn can_swap(dim : Int32, grid : Int32) -> Bool {
  let cells = cells_of(dim, grid)
  if cells < 2 {
    return false
  }
  let start = Tokens::new(dim, grid, [0, 1])
  let goal = encode([1, 0], cells)
  let seen : Map[Int32, Bool] = Map([])
  seen[encode(start.pos, cells)] = true
  let queue : Array[Tokens] = [start]
  let mut head = 0
  while head < queue.length() {
    let t = queue[head]
    head = head + 1
    if encode(t.pos, cells) == goal {
      return true
    }
    for nb in neighbours(t) {
      if seen.get(nb) is None {
        seen[nb] = true
        queue.push(Tokens::new(dim, grid, decode(nb, cells, 2)))
      }
    }
  }
  false
}

///|
/// `k!`, the expected number of components in dimension one.
pub fn factorial(k : Int32) -> Int32 {
  let mut r = 1
  for i in 1..<=k {
    r = r * i
  }
  r
}
