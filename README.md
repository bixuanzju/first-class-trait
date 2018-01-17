# SEDEL

## Paper with Appendix and Proofs

[paper-appendix.pdf](paper-appendix.pdf)

## Build and Run

This project can be built with
[cabal](https://www.haskell.org/cabal/download.html) or
[stack](https://docs.haskellstack.org/en/stable/README/).

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
- type `:q` to quit
- type `:load` to load a file
- type `:?` for usage

```
> :load examples/case_study.sl 
Typing result
: String

Evaluation result
=> "add1(var x = 3.0; var y = 4.0; (if (x < y) then (x + 2.0) else (y + 3.0))) = 6.0"
```

## Quick Reference

A program consists of list of declarations (separated by `;`), ended with a `main` declaration.
Like Haskell, a line comment starts with `--` and a comment block is wrapped by
`{-` and `-}`. 

* Primitive type: `Int`, `Bool`, `Double, ``String`
* Top type/value: `() : Top`
* Type annotation: `2 : Int`
* Merge: `true ,, 3`
* Intersection type: `Bool & (Int -> Int)`
* If: `if x == 0 then true else false`
* λ term: `(\x -> x+1) : Int -> Int`
* Λ term: `/\ (A * Int) . (\x -> x) : A -> A`
* Disjoint (universal) quantification: `forall (A*Int) . A -> A`
* Term declaration: `id A (x : A) = x`
* Type declaration: `type Person = {name : String, male : Bool}`
* Traits: `trait [self : Person] => { age = 42 }`


## Examples and Case Study

See the [examples/](./examples/) directory, in particular:
- JS examples in Section 2: [examples/overview.js](./examples/overview.js)
- SEDEL examples in Section 2: [examples/overview2.sl](./examples/overview2.sl)
- SEDEL examples in Section 3: [examples/overview2.sl](./examples/overview2.sl)
- Object Algebra example in Section 5: [examples/application.sl](./examples/application.sl)
- Case study in Section 5: [examples/case_study.sl](./examples/case_study.sl)

All examples can be tested:

```
stack test
```
