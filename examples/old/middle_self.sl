--> "((3.0 = 3.0) and (2.0 = 2.0) = 5.0) and (3.0 = 3.0)\n8.0"

type IEval = { eval : Double };

type IPrint = { print : String };

type GExpAlg[In, Out] = {
  lit : Double -> Out,
  add : In -> In -> Out
};

type ExpAlg[E] = GExpAlg[E, E];

type Exp = { accept : forall E . ExpAlg[E] -> E };

trait evalAlg : ExpAlg[IEval] { self =>
  eval@(lit x)   = x;
  eval@(add x y) = x.eval + y.eval
};

e1 : Exp = { accept E f = f.add (f.add (f.lit 3) (f.lit 2)) (f.lit 3) };

trait printAlg2 : GExpAlg[IEval & IPrint, IPrint] { fself =>
  print@(lit x)     = x.toString;
  print@(add e1 e2) = "(" ++ e1.print ++ " = " ++ e1.eval.toString ++ ") and (" ++ e2.print ++ " = " ++ e2.eval.toString ++ ")"
};

trait combine A [B * A] (f : Trait[ExpAlg[A]], g : Trait[GExpAlg[A & B, B]]) inherits f & g {};

newAlg = combine IEval IPrint evalAlg printAlg2;

o = new[ExpAlg[IEval & IPrint]] newAlg;

main = (e1.accept (IEval & IPrint) o).print ++ "\n" ++ (e1.accept (IEval & IPrint) o).eval.toString
