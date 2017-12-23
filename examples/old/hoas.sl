--> 4.0

{-

Embedding a higher-order domain-specific language (simply-typed lambda-calculus
with conditionals and constants) with a selectable evaluation order: CBV and CBN

http://okmij.org/ftp/tagless-final/call_by_any.ml

-}


type Arr[A, B] = (T -> A) -> (T -> B)

type BindAlg[Expr[_]] = {
  lam : forall A B. (Expr[A] -> Expr[B]) -> Expr[Arr[A,B]]
}

type IEval[E] = T -> E

type ExprAlg[Expr[_]] = {
  lit : Double -> Expr[Double],
  add : Expr[Double] -> Expr[Double] -> Expr[Double],
  app : forall A B. Expr[Arr[A,B]] -> Expr[A] -> Expr[B],
  bot : forall A. Expr[A]
}

trait evalAlg : ExprAlg[IEval] { self =>
  def lit n = \_ -> n
  def add e1 e2 = \_ -> e1() + e2()
  def app A B e1 e2 = \_ -> e1() e2()
  def bot A = \_ -> let x : A = x in x
}

type MulAlg[Expr[_]] = ExprAlg[Expr] & {
  mul : Expr[Double] -> Expr[Double] -> Expr[Double]
}

trait evalMul inherits evalAlg : MulAlg[IEval] { self =>
  def mul e1 e2 = \_ -> e1() * e2()
}


type BoolAlg[Expr[_]] = MulAlg[Expr] & {
  bool : Bool -> Expr[Bool],
  le : Expr[Double] -> Expr[Double] -> Expr[Bool],
  iff : forall A. Expr[Bool] -> Expr[A] -> Expr[A] -> Expr[A]

}

trait evalBool inherits evalMul : BoolAlg[IEval] { self =>
  def bool b = \_ -> b
  def le e2 e3 = \_ -> e2() < e3()
  def iff A be et ee = \_ -> if be() then et() else ee()
}


type TermAlg[Expr[_]] = BoolAlg[Expr] & BindAlg[Expr]

trait evalBindCBN : BindAlg[IEval] { self =>
  def lam A B f = \_ -> f
}
trait evalBindCBV  : BindAlg[IEval] { self =>
  def lam A B f = \_ -> \y -> let yv : A = y() in f (\_ -> yv)
}

type Term = {
  accept : TermAlg[IEval] -> IEval[Double]
}


def evaluator (o : Trait[BindAlg[IEval]]) (e : Term)  =
  e.accept (new[TermAlg[IEval]] evalBool & o)


-- (\x -> 4) bot
def ex : Term = {
  accept = \f -> f.app Double Double (f.lam Double Double (\x -> f.lit 4)) (f.bot Double)
}
main = (evaluator evalBindCBN ex)()


{-
-- Infinite loop
main = (evaluator evalBindCBV ex)()
-}
