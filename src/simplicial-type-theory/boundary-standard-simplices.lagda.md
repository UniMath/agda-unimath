# The boundary of the standard simplices

```agda
module simplicial-type-theory.boundary-standard-simplices where
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

open import simplicial-type-theory.directed-edges
open import simplicial-type-theory.directed-interval-type
open import simplicial-type-theory.inequality-directed-interval-type
open import simplicial-type-theory.simplicial-arrows
open import simplicial-type-theory.simplicial-cubes
open import simplicial-type-theory.standard-simplices

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

### The boundary of the standard simplices

```agda
subtype-auxillary-face-standard-simplex :
  (n r : ℕ) → subtype lzero (simplicial-cube n)
subtype-auxillary-face-standard-simplex 0 _ _ =
  empty-Prop
subtype-auxillary-face-standard-simplex 1 0 x =
  Id-Prop 𝟚-Set x 0₂
subtype-auxillary-face-standard-simplex 1 (succ-ℕ _) x =
  empty-Prop
subtype-auxillary-face-standard-simplex 2 zero-ℕ (x , y) =
  Id-Prop 𝟚-Set x y
subtype-auxillary-face-standard-simplex 2 (succ-ℕ r) (x , y) =
  subtype-auxillary-face-standard-simplex 1 r y
subtype-auxillary-face-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) 0 (x , y , u) =
  ( Id-Prop 𝟚-Set x y) ∧
  ( subtype-standard-simplex (succ-ℕ (succ-ℕ n)) (y , u))
subtype-auxillary-face-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) (x , y , u) =
  ( leq-𝟚-Prop y x) ∧
  ( subtype-auxillary-face-standard-simplex (succ-ℕ (succ-ℕ n)) r (y , u))

subtype-first-face-standard-simplex :
  (n : ℕ) → subtype lzero (simplicial-cube n)
subtype-first-face-standard-simplex 0 _ = empty-Prop
subtype-first-face-standard-simplex 1 x = Id-Prop 𝟚-Set 1₂ x
subtype-first-face-standard-simplex 2 (x , _) = Id-Prop 𝟚-Set 1₂ x
subtype-first-face-standard-simplex (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , u) =
  Id-Prop 𝟚-Set 1₂ x ∧ subtype-standard-simplex (succ-ℕ (succ-ℕ n)) u

subtype-face-standard-simplex : (n r : ℕ) → subtype lzero (simplicial-cube n)
subtype-face-standard-simplex n 0 =
  subtype-first-face-standard-simplex n
subtype-face-standard-simplex n (succ-ℕ r) =
  subtype-auxillary-face-standard-simplex n r
```

> These definitions would've been a bit simpler if we used list induction.

```agda
subtype-faces-up-to-standard-simplex :
  (n k : ℕ) → subtype lzero (simplicial-cube n)
subtype-faces-up-to-standard-simplex n 0 = subtype-face-standard-simplex n 0
subtype-faces-up-to-standard-simplex n (succ-ℕ k) =
  union-subtype
    ( subtype-face-standard-simplex n (succ-ℕ k))
    ( subtype-faces-up-to-standard-simplex n k)

subtype-boundary-standard-simplex : (n : ℕ) → subtype lzero (simplicial-cube n)
subtype-boundary-standard-simplex n = subtype-faces-up-to-standard-simplex n n

∂Δ : ℕ → UU
∂Δ = type-subtype ∘ subtype-boundary-standard-simplex

-- TODO: add alternative definition
```

### The boundary of the standard simplex is included in the standard simplex

```agda
leq-subtype-auxillary-face-standard-simplex-standard-simplex :
  (n r : ℕ) →
  subtype-auxillary-face-standard-simplex n r ⊆ subtype-standard-simplex n
leq-subtype-auxillary-face-standard-simplex-standard-simplex 1 0 _ _ =
  star
leq-subtype-auxillary-face-standard-simplex-standard-simplex 2 0 (x , y) =
  leq-inv-eq-𝟚
leq-subtype-auxillary-face-standard-simplex-standard-simplex 2 1 _ =
  min-leq-eq-𝟚
leq-subtype-auxillary-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) 0 _ (x=y , d) =
  ( leq-inv-eq-𝟚 x=y , d)
leq-subtype-auxillary-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) (_ , u) (x≥y , f) =
  ( x≥y ,
    leq-subtype-auxillary-face-standard-simplex-standard-simplex
      ( succ-ℕ (succ-ℕ n)) r u f)

leq-subtype-face-standard-simplex-standard-simplex :
  (n r : ℕ) → subtype-face-standard-simplex n r ⊆ subtype-standard-simplex n
leq-subtype-face-standard-simplex-standard-simplex 1 0 _ _ =
  star
leq-subtype-face-standard-simplex-standard-simplex 1 (succ-ℕ r) _ _ =
  star
leq-subtype-face-standard-simplex-standard-simplex 2 0 _ =
  max-leq-eq-𝟚 ∘ inv
leq-subtype-face-standard-simplex-standard-simplex 2 (succ-ℕ r) =
  leq-subtype-auxillary-face-standard-simplex-standard-simplex 2 r
leq-subtype-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) 0 _ (1=x , p) =
  ( max-leq-eq-𝟚 (inv 1=x) , p)
leq-subtype-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) =
  leq-subtype-auxillary-face-standard-simplex-standard-simplex
    ( succ-ℕ (succ-ℕ (succ-ℕ n)))
    ( r)

leq-subtype-faces-up-to-standard-simplex-standard-simplex :
  (n k : ℕ) →
  subtype-faces-up-to-standard-simplex n k ⊆ subtype-standard-simplex n
leq-subtype-faces-up-to-standard-simplex-standard-simplex n 0 =
  leq-subtype-face-standard-simplex-standard-simplex n 0
leq-subtype-faces-up-to-standard-simplex-standard-simplex n (succ-ℕ k) x =
  elim-disjunction
    ( subtype-standard-simplex n x)
    ( leq-subtype-face-standard-simplex-standard-simplex n (succ-ℕ k) x)
    ( leq-subtype-faces-up-to-standard-simplex-standard-simplex n k x)

leq-subtype-boundary-standard-simplex-standard-simplex :
  (n : ℕ) → subtype-boundary-standard-simplex n ⊆ subtype-standard-simplex n
leq-subtype-boundary-standard-simplex-standard-simplex n =
  leq-subtype-faces-up-to-standard-simplex-standard-simplex n n

inclusion-boundary-standard-simplex : (n : ℕ) → ∂Δ n → Δ n
inclusion-boundary-standard-simplex n =
  tot (leq-subtype-boundary-standard-simplex-standard-simplex n)
```

## Properties

### The standard 𝑛-simplex is a retract of the directed 𝑛-cube

This remains to be formalized. Lemma 4.2.2 {{#cite MR23b}}

## References

{{#bibliography}}
