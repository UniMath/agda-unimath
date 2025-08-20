# Standard simplices

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.standard-simplices
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
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

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.cubes I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

### The standard simplices

$$x₁ ≥ x₂ ≥ … ≥ xₙ₋₁ ≥ xₙ$$ (in the right-associated cube)

```agda
subtype-standard-simplex : (n : ℕ) → subtype I2 (directed-cube n)
subtype-standard-simplex 0 _ =
  raise-unit-Prop I2
subtype-standard-simplex 1 _ =
  raise-unit-Prop I2
subtype-standard-simplex 2 (x , y) =
  leq-Δ¹-Prop y x
subtype-standard-simplex (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , y , u) =
  conjunction-Prop
    ( subtype-standard-simplex 2 (x , y))
    ( subtype-standard-simplex (succ-ℕ (succ-ℕ n)) (y , u))

predicate-standard-simplex : (n : ℕ) → directed-cube n → UU I2
predicate-standard-simplex = is-in-subtype ∘ subtype-standard-simplex

standard-simplex : ℕ → UU (I1 ⊔ I2)
standard-simplex = type-subtype ∘ subtype-standard-simplex

Δ : ℕ → UU (I1 ⊔ I2)
Δ = standard-simplex
```

## Properties

### The standard 𝑛-simplex is a retract of the directed 𝑛-cube

This remains to be formalized. Lemma 4.2.2 {{#cite MR23b}}

## References

{{#bibliography}}
