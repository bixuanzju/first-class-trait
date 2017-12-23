# SEDEL: Safe and Expressive Delegation-Based Programming

SEDEL is a new statically-typed and delegation-based object-oriented programming
language that supports dynamic composable traits, disjoint polymorphism,
intersection types and a merge construct.

SEDEL is written in the Haskell language.

## Build and Run

This project can be built
with [cabal](https://www.haskell.org/cabal/download.html)
or [stack](https://docs.haskellstack.org/en/stable/README/).

* cabal
```
cabal sandbox init
cabal install --only-dependencies
cabal build
cabal exec SEDEL-exe
```

* stack
```
stack build
stack exec SEDEL-exe
```

## REPL

The REPL prompt is `>`:
- type `:q` to quit or input any expression in the source language to check its
result
- type `:load` to load a file

```
> 2
Typing result
: Double

Evaluation result
=> 2.0
```

## Quick Reference

A program consists of list of declarations, ending with a single expression.
Like Haskell, a line comment starts with `--` and a comment block is wrapped by
`{-` and `-}`. Declarations include type (`type ...`) and term (`def/defrec ...`) declarations:

```
program := decl ... decl expr
decl    := def ... | type ... | defrec ...
```


* Primitive type: `Double`, `Bool`, `String`
* Top type/value: `() : T`
* Type annotation: `2 : Double`
* Merge: `true ,, 3`
* Intersection type: `Bool & (Double -> Double)`
* If: `if x == 0 then true else false`
* λ term: `(\x -> x+1) : Double -> Double`
* Λ term: `/\ (A * Double) . (\x -> x) : A -> A`
* Disjoint (universal) quantification: `forall (A*Int) . A -> A`
* Term declaration: `def id A (x : A) = x`
* Type declaration: `type Person = {name : String, male : Bool}`

## Examples and Case Study

See the [examples/](./examples/) directory. All examples can be tested:

```
stack test
```
