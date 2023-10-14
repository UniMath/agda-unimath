# Transfinite composition of maps

```agda
module foundation.transfinite-composition-of-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.cones-over-towers
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-fibers-of-maps
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.limits-towers
open import foundation.maps-of-towers
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.towers-of-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universal-property-limits-of-towers
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.diagonal-maps-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
```

</details>

## Idea

Given an infinite [sequence](foundation.dependent-sequences.md) of maps, i.e. a
[tower](foundation.towers-of-types.md) `fₙ`:

```text
      ⋯         fₙ       ⋯       f₁       f₀
  ⋯ ----> Aₙ₊₁ ----> Aₙ ----> ⋯ ----> A₁ ----> A₀,
```

then we can form the **transfinite composition** of `fₙ` by taking the canonical
map from the [standard limit of the tower](foundation.limits-towers.md) into
`A₀`.

## Definitions

### The transfinite composition of a tower of maps

```agda
module _
  {l : Level} (f : Tower l)
  where

  transfinite-comp : standard-limit-Tower f → type-Tower f 0
  transfinite-comp x = sequence-standard-limit-Tower f x 0
```
