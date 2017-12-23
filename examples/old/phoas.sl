--> "(((\\x0.0 -> (x0.0 * (7.0 + 2.0))) 1.0) + 2.0)"

type K[A, _] = A

type I[A] = A

type ExprAlg[Expr[_[_], _], F[_]] = {
  lit : Double -> Expr[F, Double],
  add : Expr[F, Double] -> Expr[F, Double] -> Expr[F, Double],
  var : forall A. F[A] -> Expr[F, A],
  lam : forall A B. (F[A] -> Expr[F, B]) -> Expr[F, A -> B],
  app : forall A B. Expr[F, A -> B] -> Expr[F, A] -> Expr[F, B]
}

type IEval[_[_], E] = { eval : E }

type IPrint[_[_], _] = { print : Double -> String }

trait evalAlg : ExprAlg[IEval, I] { self =>
  def lit x         = { eval = x }
  def add x y       = { eval = x.eval + y.eval }
  def var A x       = { eval = x }
  def lam A B f     = { eval = \x -> (f x).eval }
  def app A B e1 e2 = { eval = e1.eval e2.eval }
}


trait printAlg : ExprAlg[IPrint, K[String]] { self =>
  def lit x = { print = \_ -> x.toString }
  def add e1 e2 = { print = \h -> "(" ++ e1.print h ++ " + " ++ e2.print h ++ ")" }
  def var A x = { print = \_ -> x }
  def lam A B e =
    { print = \h -> let x : String = "x" ++ h.toString
                    in "(\\" ++ x ++ " -> " ++
                       (e x).print (h + 1) ++ ")"
    }
  def app A B e1 e2 = { print = \h -> "(" ++ e1.print h ++ " " ++ e2.print h ++ ")" }
}


type MulExprAlg[Expr[_[_], _], F[_]] = ExprAlg[Expr, F] & {
  mul : Expr[F, Double] -> Expr[F, Double] -> Expr[F, Double]
}

trait mulEvalAlg inherits evalAlg : MulExprAlg[IEval, I] { self =>
  def mul x y = { eval = x.eval * y.eval }
}

trait mulPrintAlg inherits printAlg : MulExprAlg[IPrint, K[String]] { self =>
  def mul e1 e2 = { print = \h -> "(" ++ e1.print h ++ " * " ++ e2.print h ++ ")" }
}


def e1 (f : MulExprAlg[IPrint, K[String]]) = f.add (f.lit 7) (f.lit 2)

def e2 (f : MulExprAlg[IPrint, K[String]]) = f.lam String String (\x -> f.mul (f.var String x) (e1 f))

def e3 (f : MulExprAlg[IPrint, K[String]]) =  f.add (f.app String String (e2 f) (f.lit 1)) (f.lit 2)

main = (e3 (new[MulExprAlg[IPrint, K[String]]] mulPrintAlg)).print 0
