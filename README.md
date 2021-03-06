# Scientific
Scientific numbers in any base built on `Fin`.
`Scientific b` is actually isomorphic to the numbers representable as a finite sum of powers of the base `b`.

## Usage
One should note that the arithmetic built on `Fin` is quite slow, but still might be useful, since it has arbitrary precision.

```idris
x, y : Scientific 10
x = 42069
y = -1337

Data.Scientific> prettyShowScientific $ x + y
"4.0732e4"
```

## Work in progress
I would appreciate some help with this:
* can't have implementation `Num (Scientific (S (S b)))`, since the methods need access to `b`

There is still some stuff I want to do:
* `toInteger`, `toNat`, `toFin`
* `fromDouble`, `toDouble`
* multiplication `*`
* switching base from `b` to `n * b` with `n : Nat`
* parsing with `Text.Token`, `Text.Lexer` and `Text.Parser`
* use in a JSON library

And some things should be possible but are a little far fetched at the moment:
* division by factors of the base `b`
