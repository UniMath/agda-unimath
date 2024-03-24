# Iterated loop spaces

```agda
module synthetic-homotopy-theory.iterated-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.iterating-functions
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

An **iterated loop space** `Ωⁿ A` is the
[pointed type](structured-types.pointed-types.md) obtained by `n` times
[iterating](foundation.iterating-functions.md) the
[loop space](synthetic-homotopy-theory.loop-spaces.md) functor
`Ω : Pointed-Type → Pointed-Type`.

## Definitions

### Iterated loop spaces

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space n = iterate n Ω
```

### Iterated loop spaces of H-spaces

```agda
module _
  {l : Level}
  where

  iterated-loop-space-H-Space : ℕ → H-Space l → H-Space l
  iterated-loop-space-H-Space zero-ℕ X = X
  iterated-loop-space-H-Space (succ-ℕ n) X =
    Ω-H-Space (iterated-loop-space n (pointed-type-H-Space X))
```

## See also

- [Double loop spaces](synthetic-homotopy-theory.double-loop-spaces.md)
- [Triple loop spaces](synthetic-homotopy-theory.triple-loop-spaces.md)
