///|
/// # Readback
///
/// Values contain host closures, so they cannot be printed structurally.
/// `quote` **probes** each closure at a fresh neutral and prints the
/// result: normalisation by evaluation with a syntactic readback.  It is
/// how every test in this package states its expected answer.

///|
/// Binder names assigned by `quote`, keyed by the kernel's neutral id.
///
/// The kernel allocates fresh dimensions while *evaluating* (every filler
/// needs one), and those allocations must not leak into printed names:
/// otherwise two identical normal forms would print differently just
/// because one of them took more reduction steps.  So `quote` keeps its
/// own counter and prints binders in the order it introduces them.
let quote_names : Map[Int32, Int32] = Map([])

///|
let quote_state : Fresh = Fresh::{ next: 0, }

///|
fn quote_binder() -> Int32 {
  let v = fresh_dim()
  quote_names[v] = quote_state.next
  quote_state.next = quote_state.next + 1
  v
}

///|
fn name_of(k : Int32) -> String {
  match quote_names.get(k) {
    Some(n) => "x\{n}"
    None => {
      // A *free* direction (one the kernel allocated, not a binder) also
      // gets a quote-local name, from the same supply.  Otherwise the
      // rendering of a normal form would depend on how many directions
      // the kernel happened to allocate before it was printed.
      let n = quote_state.next
      quote_state.next = n + 1
      quote_names[k] = n
      "x\{n}"
    }
  }
}

///|
pub fn Val::quote(self : Val, depth : Int32) -> String {
  if depth <= 0 {
    return "…"
  }
  let d = depth - 1
  match self {
    VU => "U"
    VFin(n) => "Fin(\{n})"
    VNat => "Nat"
    VLit(k) => "#\{k}"
    VZero => "zero"
    VSuc(n) => "suc(" + n.quote(d) + ")"
    VSplit(n, brs, sc) => {
      let mut out = "case[" + sc.quote(d) + " : Fin(\{n})"
      for b in brs {
        out += " | " + b.quote(d)
      }
      out + "]"
    }
    VNatRec(z, step, sc) => {
      let v = quote_binder()
      let w = quote_binder()
      let body = vapp(step.at(VNe(v)), VNe(w)).quote(d)
      let zq = z.quote(d)
      let sq = sc.quote(d)
      let nm = name_of(v)
      let im = name_of(w)
      "natrec[" + sq + "](" + zq + "; " + nm + " " + im + "." + body + ")"
    }
    VCircle => "S¹"
    VBase => "base"
    VLoop(r) => "loop(" + dim_render(r) + ")"
    VSusp(a) => "Susp(" + a.quote(d) + ")"
    VNorth => "north"
    VSouth => "south"
    VMerid(_, a, r) => "merid(" + a.quote(d) + ")(" + dim_render(r) + ")"
    VTrunc(a) => "∥" + a.quote(d) + "∥"
    VInc(a) => "inc(" + a.quote(d) + ")"
    VSq(_, x, y, r) =>
      "sq(" + x.quote(d) + ", " + y.quote(d) + ")(" + dim_render(r) + ")"
    VHComp(ty, tube, cap) => {
      let mut out = "hcomp[" + ty.quote(d) + " | " + cap.quote(d)
      for br in tube.branches {
        let v = quote_binder()
        let body = br.tm.at(@cubical.DVar(v)).quote(d)
        out += " | " + cof_render(br.cof) + " ↦ " + name_of(v) + "." + body
      }
      out + "]"
    }
    VCircRec(_, b, l, x) =>
      "S¹-rec(" + b.quote(d) + "; " + l.quote(d) + ")(" + x.quote(d) + ")"
    VTruncRec(_, f, _, x) =>
      "∥∥-rec(" + f.quote(d) + ")(" + x.quote(d) + ")"
    VSuspRec(_, n, st, m, x) =>
      "Susp-rec(" +
      n.quote(d) +
      "; " +
      st.quote(d) +
      "; " +
      m.quote(d) +
      ")(" +
      x.quote(d) +
      ")"
    VCoeq(b, _, _) => "Coeq(" + b.quote(d) + ")"
    VCoeqInc(b) => "cinc(" + b.quote(d) + ")"
    VCoeqRel(a, r) => "rel(" + a.quote(d) + ")(" + dim_render(r) + ")"
    VCoeqRec(_, h, _, x) => "Coeq-rec(" + h.quote(d) + ")(" + x.quote(d) + ")"
    VNe(k) => name_of(k)
    VPi(a, c) => {
      let v = quote_binder()
      let dom = a.quote(d)
      let cod = c.at(VNe(v)).quote(d)
      let nm = name_of(v)
      "Π(" + nm + " : " + dom + "). " + cod
    }
    VSig(a, c) => {
      let v = quote_binder()
      let dom = a.quote(d)
      let cod = c.at(VNe(v)).quote(d)
      let nm = name_of(v)
      "Σ(" + nm + " : " + dom + "). " + cod
    }
    VPath(fam, a, b) => {
      let v = quote_binder()
      let body = fam.at(@cubical.DVar(v)).quote(d)
      let l = a.quote(d)
      let r = b.quote(d)
      let nm = name_of(v)
      "Path(" + nm + "." + body + ") " + l + " " + r
    }
    VGlue(a, brs) => {
      let mut out = "Glue[" + a.quote(d)
      for b in brs {
        let v = quote_binder()
        let t = b.ty.quote(d)
        let e = vapp(b.eq.fwd, VNe(v)).quote(d)
        out += " | " + cof_render(b.cof) + " ↦ (" + t + ", e=" + e + ")"
      }
      out + "]"
    }
    VLam(c) => {
      let v = quote_binder()
      let body = c.at(VNe(v)).quote(d)
      let nm = name_of(v)
      "λ" + nm + ". " + body
    }
    VPair(a, b) => {
      let l = a.quote(d)
      let r = b.quote(d)
      "(\{l}, \{r})"
    }
    VPLam(c) => {
      let v = quote_binder()
      let body = c.at(@cubical.DVar(v)).quote(d)
      let nm = name_of(v)
      "<" + nm + "> " + body
    }
    VGlued(brs, a) => {
      let mut out = "glue[" + a.quote(d)
      for b in brs {
        out += " | " + cof_render(b.cof) + " ↦ " + b.tm.quote(d)
      }
      out + "]"
    }
  }
}

///|
/// Quote with a *fixed* probe counter, so two quotations of the same
/// normal form are literally the same string: the α-invariant comparison
/// used by the tests.
pub fn quote_norm(v : Val, depth : Int32) -> String {
  let save = fresh_dims.next
  let save_next = quote_state.next
  let save_names : Map[Int32, Int32] = Map([])
  for k, n in quote_names {
    save_names[k] = n
  }
  quote_names.clear()
  quote_state.next = 0
  let s = v.quote(depth)
  fresh_dims.next = save
  quote_state.next = save_next
  quote_names.clear()
  for k, n in save_names {
    quote_names[k] = n
  }
  s
}

///|
pub impl Debug for Val with fn to_repr(self) {
  Repr::literal(quote_norm(self, 8))
}

///|
/// Render a dimension.
pub fn dim_render(r : Dim) -> String {
  match r {
    @cubical.DZero => "0"
    @cubical.DOne => "1"
    @cubical.DVar(i) => name_of(i)
    @cubical.DNot(s) => "~" + dim_render(s)
    @cubical.DAnd(a, b) => "(" + dim_render(a) + "∧" + dim_render(b) + ")"
    @cubical.DOr(a, b) => "(" + dim_render(a) + "∨" + dim_render(b) + ")"
  }
}

///|
/// Render a cofibration.
pub fn cof_render(c : Cof) -> String {
  match c {
    @cubical.CBot => "⊥"
    @cubical.CTop => "⊤"
    @cubical.CEq(r, k) => {
      let e = if k == 0 { "0" } else { "1" }
      "(" + dim_render(r) + "=" + e + ")"
    }
    @cubical.CAnd(a, b) => "(" + cof_render(a) + "∧" + cof_render(b) + ")"
    @cubical.COr(a, b) => "(" + cof_render(a) + "∨" + cof_render(b) + ")"
  }
}
