type Var UInt derive (Show, Eq, Compare)


enum Term {
  Constant(BigInt)
  Var(Var)
  Add(Term, Term)
  Mul(BigInt, Term)
} derive(Show)


let zero : Term = Constant(0)

fn op_add(self : Term, operand : Term) -> Term {
  // Naive 
  Add(self, operand)
}

fn mul(self : Term, n : BigInt) -> Term {
  if n == 0 {
    return zero
  }
  // assume self is canonical form
  match self {
    Add(Mul(c, Var(_) as x), r) => {
      Add(Mul(c * n, x), mul(r, n))
    }
    Constant(k) => Constant(k * n)
    _ => abort("not canonical")
  }
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





