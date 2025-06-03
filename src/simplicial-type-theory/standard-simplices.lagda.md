# Standard simplices

```agda
module simplicial-type-theory.standard-simplices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unions-subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import simplicial-type-theory.arrows
open import simplicial-type-theory.directed-cubes
open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type I
open import simplicial-type-theory.inequality-directed-interval-type I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

### The standard simplices

$$x₁ ≥ x₂ ≥ … ≥ xₙ₋₁ ≥ xₙ$$ (in the right-associated cube)

```agda
subtype-standard-simplex : (n : ℕ) → subtype lzero (simplicial-cube n)
subtype-standard-simplex 0 _ =
  unit-Prop
subtype-standard-simplex 1 _ =
  unit-Prop
subtype-standard-simplex 2 (x , y) =
  leq-Δ¹-Prop y x
subtype-standard-simplex (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , y , u) =
  conjunction-Prop
    ( subtype-standard-simplex 2 (x , y))
    ( subtype-standard-simplex (succ-ℕ (succ-ℕ n)) (y , u))

predicate-standard-simplex : (n : ℕ) → simplicial-cube n → UU
predicate-standard-simplex = is-in-subtype ∘ subtype-standard-simplex

standard-simplex : ℕ → UU
standard-simplex = type-subtype ∘ subtype-standard-simplex

Δ : ℕ → UU
Δ = standard-simplex
```

## Properties

### The standard 𝑛-simplex is a retract of the directed 𝑛-cube

This remains to be formalized. Lemma 4.2.2 {{#cite MR23b}}

## References

{{#bibliography}}
