# Simplicial cubes

```agda
module simplicial-type-theory.simplicial-cubes where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.directed-interval-type
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) 𝑛, the
{{#concept "standard simplicial 𝑛-cube" Disambiguation="simplicial type theory" Agda=simplicial-cube}}
consists of 𝑛-fold pairs of elements of the
[directed interval](simplicial-type-theory.directed-interval-type.md). The
standard simplicial 0-cube is defined to be the
[unit type](foundation.unit-type.md).

## Definitions

### The standard simplicial cubes

```agda
simplicial-cube : ℕ → UU lzero
simplicial-cube 0 = unit
simplicial-cube 1 = 𝟚
simplicial-cube (succ-ℕ (succ-ℕ n)) = 𝟚 × simplicial-cube (succ-ℕ n)
```

### The standard left-associated simplicial cubes

```agda
left-associated-simplicial-cube : ℕ → UU lzero
left-associated-simplicial-cube 0 = unit
left-associated-simplicial-cube 1 = 𝟚
left-associated-simplicial-cube (succ-ℕ (succ-ℕ n)) =
  (left-associated-simplicial-cube (succ-ℕ n)) × 𝟚
```

### The standard simplicial power cubes

```agda
pow-simplicial-cube : ℕ → UU lzero
pow-simplicial-cube 0 = unit
pow-simplicial-cube 1 = 𝟚
pow-simplicial-cube (succ-ℕ (succ-ℕ n)) =
  (pow-simplicial-cube (succ-ℕ n)) × (pow-simplicial-cube (succ-ℕ n))
```
