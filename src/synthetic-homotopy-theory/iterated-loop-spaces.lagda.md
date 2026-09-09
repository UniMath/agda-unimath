# Iterated loop spaces

```agda
module synthetic-homotopy-theory.iterated-loop-spaces where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.iterating-functions
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.iterated-successors-truncation-levels

open import structured-types.h-spaces
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

The
{{#concept "iterated loop space" Disambiguation="of a pointed type" Agda=iterated-loop-space}}
`ΩⁿA` of a [pointed type](structured-types.pointed-types.md) `A` is obtained by
[iteratively](foundation.iterating-functions.md) applying the
[loop space](synthetic-homotopy-theory.loop-spaces.md) operation `Ω` to `A`.

## Definitions

### Iterated loop spaces

```agda
module _
  {l : Level}
  where

  iterated-loop-space : ℕ → Pointed-Type l → Pointed-Type l
  iterated-loop-space n = iterate n Ω

  type-iterated-loop-space : ℕ → Pointed-Type l → UU l
  type-iterated-loop-space n A = type-Pointed-Type (iterated-loop-space n A)

  point-iterated-loop-space :
    (n : ℕ) (A : Pointed-Type l) → type-iterated-loop-space n A
  point-iterated-loop-space n A = point-Pointed-Type (iterated-loop-space n A)
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

### If A is (𝑛+𝑘)-truncated then ΩⁿA is 𝑘-truncated

```agda
is-trunc-iterated-loop-space :
  {l : Level} (n : ℕ) (k : 𝕋) (A : Pointed-Type l) →
  is-trunc (iterate-succ-𝕋 n k) (type-Pointed-Type A) →
  is-trunc k (type-iterated-loop-space n A)
is-trunc-iterated-loop-space zero-ℕ k A H = H
is-trunc-iterated-loop-space (succ-ℕ n) k A H =
  is-trunc-Ω k
    ( iterated-loop-space n A)
    ( is-trunc-iterated-loop-space n (succ-𝕋 k) A H)
```

## See also

- [Double loop spaces](synthetic-homotopy-theory.double-loop-spaces.md)
- [Triple loop spaces](synthetic-homotopy-theory.triple-loop-spaces.md)

## External links

- [Loop space](https://www.wikidata.org/wiki/Q2066070) on Wikidata
- [Function iteration](https://www.wikidata.org/wiki/Q5254619) on Wikidata
