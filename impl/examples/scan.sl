--> true

type GCircuitAlg[In, Out] = {
  identity : Double -> Out,
  fan : Double -> Out,
  beside : In -> In -> Out,
  above : In -> In -> Out
};

type CircuitAlg[E] = GCircuitAlg[E, E];

type Circuit = { accept : forall E. CircuitAlg[E] -> E };

-- Example
e1 : Circuit = { accept E f =
  f.above (f.beside (f.fan 2) (f.fan 2))
          (f.beside (f.beside (f.identity 1) (f.fan 2)) (f.identity 1))
};

-- Width interpretation
type Width = { width : Double };

trait widthCircuit [ self : Top] => {
  identity (n : Double)   = { width = n };
  fan (n : Double)        = { width = n };
  beside (c1 : Width) (c2 : Width) = { width = c1.width + c2.width };
  above (c1 : Width) (c2 : Width)  = { width = c1.width }
} : CircuitAlg[Width] ;

width (c : Circuit) : Double = (c.accept Width (new[CircuitAlg[Width]] widthCircuit)).width;


-- Depth interpretation
type Depth = { depth : Double };

max (x : Double) (y : Double) = if x > y then x else y;

trait depthCircuit  => {
  identity (n : Double)   = { depth = 0 };
  fan (n : Double)        = { depth = 1 };
  beside (c1 : Depth) (c2 : Depth) = { depth = max c1.depth c2.depth };
  above (c1 : Depth) (c2 : Depth)  = { depth = c1.depth + c2.depth }
} : CircuitAlg[Depth] ;

depth (c : Circuit) : Double = (c.accept Depth (new[CircuitAlg[Depth]] depthCircuit)).depth;

-- Well-sized interpretation

type WellSized = { wellSized : Bool };

trait sizedCircuit  => {
  identity (n : Double)   = { wellSized = true };
  fan (n : Double)        = { wellSized = true };
  beside (c1 : Width & WellSized) (c2 : Width & WellSized) = { wellSized = c1.wellSized && c2.wellSized };
  above (c1 : Width & WellSized) (c2 : Width & WellSized)  = { wellSized = c1.wellSized && c2.wellSized && c1.width == c2.width }
} : GCircuitAlg[Width & WellSized, WellSized] ;

merge A [B * A] (a : Trait[CircuitAlg[A]]) (b : Trait[GCircuitAlg[A & B, B]]) = trait  =>  {
  identity (n : Double)   = (new[CircuitAlg[A]] a).identity n ,, (new[GCircuitAlg[A & B, B]] b).identity n;
  fan (n : Double)        = (new[CircuitAlg[A]] a).fan n ,, (new[GCircuitAlg[A & B, B]] b).fan n;
  beside (c1 : A & B) (c2 : A & B) = (new[CircuitAlg[A]] a).beside c1 c2 ,, (new[GCircuitAlg[A & B, B]] b).beside c1 c2;
  above (c1 : A & B) (c2 : A & B)  = (new[CircuitAlg[A]] a).above c1 c2 ,, (new[GCircuitAlg[A & B, B]] b).above c1 c2
} : CircuitAlg[A & B];

alg = merge Width WellSized widthCircuit sizedCircuit;

o = new[CircuitAlg[Width & WellSized]] alg;

main = (e1.accept (Width & WellSized) o).wellSized
