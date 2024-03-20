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

### Iterated loop spaces as H-spaces

Note that the indexing is off by one in the following definition. That is, the
[H-space](structured-types.h-spaces.md)

```text
  iterated-loop-space-H-Space n X
```

is the H-space `Ωⁿ⁺¹ X`.

```agda
module _
  {l : Level}
  where

  iterated-loop-space-H-Space : ℕ → Pointed-Type l → H-Space l
  iterated-loop-space-H-Space n X = Ω-H-Space (iterated-loop-space n X)
```

## See also

- [Double loop spaces](synthetic-homotopy-theory.double-loop-spaces.md)
- [Triple loop spaces](synthetic-homotopy-theory.triple-loop-spaces.md)
