--> 10.0

type C[_] = Double

type D[H[_]] = H[Bool] -> Double

type A[B[_[_]], F[_]] = B[C] -> F[String]

def test : A[D, C] = \f -> f 5

main = test (\x -> x + 5)
