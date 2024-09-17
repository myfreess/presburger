type Var UInt derive(Show, Eq, Compare)

fn earlier_than(self : Var, v : Var) -> Bool {
  self._ < v._
}

// canonical form : c0 * x0 + ...... + cN * xN + k
// x0._ < x1._ < x2._ ...... < xN._
enum Term {
  Constant(BigInt)
  Var(Var)
  Add(Term, Term)
  Mul(BigInt, Term)
} derive(Show)

let zero : Term = Constant(0)

fn op_add(self : Term, operand : Term) -> Term {
  match (self, operand) {
    (Add(Mul(c1, Var(x1)) as p1, r1), Add(Mul(c2, Var(x2)) as p2, r2)) =>
      if x1 == x2 {
        let c = c1 + c2
        if c == 0 {
          op_add(r1, r2)
        } else {
          Add(Mul(c1 + c2, Var(x1)), op_add(r1, r2))
        }
      } else if x1.earlier_than(x2) {
        Add(p1, op_add(r1, operand))
      } else {
        Add(p2, op_add(self, r2))
      }
    (Add(Mul(_, Var(_)) as p, r), Constant(_) as k) => Add(p, op_add(r, k))
    (Constant(_) as k, Add(Mul(_, Var(_)) as p, r)) => Add(p, op_add(k, r))
    (Constant(k1), Constant(k2)) => Constant(k1 + k2)
    _ => abort("not canonical")
  }
}

fn mul(self : Term, n : BigInt) -> Term {
  if n == 0 {
    return zero
  }
  // assume self is canonical form
  match self {
    Add(Mul(c, Var(_) as x), r) => Add(Mul(c * n, x), mul(r, n))
    Constant(k) => Constant(k * n)
    _ => abort("not canonical")
  }
}

fn op_mul(self : Term, operand : Term) -> Term {
  match (self, operand) {
    (Constant(c), term) => mul(term, c)
    (term, Constant(c)) => mul(term, c)
    _ => panic()
  }
}

fn op_neg(self : Term) -> Term {
  mul(self, -1)
}

fn op_sub(self : Term, operand : Term) -> Term {
  self + -operand
}
 
struct Context {
  mut next_var : UInt
}

fn next_var(self : Context) -> Var {
  let var = self.next_var
  self.next_var += 1
  return var
}

enum Formula {
  Eq(Term, Term)
  Greater(Term, Term)
  Lesser(Term, Term)
  Div(Term, BigInt)
  PropConst(Bool)
  Conj(Formula, Formula)
  Disj(Formula, Formula)
  Negate(Formula)
  Exist(Var, Formula)
  Forall(Var, Formula)
}

fn exist(self : Context, f : (Var) -> Formula) -> Formula {
  let var = self.next_var()
  Exist(var, f(var))
}

fn forall(self : Context, f : (Var) -> Formula) -> Formula {
  let var = self.next_var()
  Forall(var, f(var))
}

fn main {
  println("presburger")
}