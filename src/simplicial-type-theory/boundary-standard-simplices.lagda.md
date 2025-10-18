# The boundary of the standard simplices

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.boundary-standard-simplices
  {I1 : Level} (I : Nontrivial-Bounded-Total-Order I1 I1)
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
open import simplicial-type-theory.standard-simplices I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Definitions

### The boundary of the standard simplices

```agda
subtype-auxillary-face-standard-simplex :
  (n r : ℕ) → subtype I1 (directed-cube n)
subtype-auxillary-face-standard-simplex 0 _ _ =
  raise-empty-Prop I1
subtype-auxillary-face-standard-simplex 1 0 x =
  Id-Prop Δ¹-Set x 0▵
subtype-auxillary-face-standard-simplex 1 (succ-ℕ _) x =
  raise-empty-Prop I1
subtype-auxillary-face-standard-simplex 2 zero-ℕ (x , y) =
  Id-Prop Δ¹-Set x y
subtype-auxillary-face-standard-simplex 2 (succ-ℕ r) (x , y) =
  subtype-auxillary-face-standard-simplex 1 r y
subtype-auxillary-face-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) 0 (x , y , u) =
  ( Id-Prop Δ¹-Set x y) ∧
  ( subtype-Δ (succ-ℕ (succ-ℕ n)) (y , u))
subtype-auxillary-face-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) (x , y , u) =
  ( leq-prop-Δ¹ y x) ∧
  ( subtype-auxillary-face-standard-simplex (succ-ℕ (succ-ℕ n)) r (y , u))

subtype-first-face-standard-simplex :
  (n : ℕ) → subtype I1 (directed-cube n)
subtype-first-face-standard-simplex 0 _ = raise-empty-Prop I1
subtype-first-face-standard-simplex 1 x = Id-Prop Δ¹-Set 1▵ x
subtype-first-face-standard-simplex 2 (x , _) = Id-Prop Δ¹-Set 1▵ x
subtype-first-face-standard-simplex (succ-ℕ (succ-ℕ (succ-ℕ n))) (x , u) =
  Id-Prop Δ¹-Set 1▵ x ∧ subtype-Δ (succ-ℕ (succ-ℕ n)) u

subtype-face-standard-simplex : (n r : ℕ) → subtype I1 (directed-cube n)
subtype-face-standard-simplex n 0 =
  subtype-first-face-standard-simplex n
subtype-face-standard-simplex n (succ-ℕ r) =
  subtype-auxillary-face-standard-simplex n r
```

> These definitions would've been a bit simpler if we used list induction.

```agda
subtype-faces-up-to-standard-simplex :
  (n k : ℕ) → subtype I1 (directed-cube n)
subtype-faces-up-to-standard-simplex n 0 = subtype-face-standard-simplex n 0
subtype-faces-up-to-standard-simplex n (succ-ℕ k) =
  union-subtype
    ( subtype-face-standard-simplex n (succ-ℕ k))
    ( subtype-faces-up-to-standard-simplex n k)

subtype-boundary-standard-simplex : (n : ℕ) → subtype I1 (directed-cube n)
subtype-boundary-standard-simplex n = subtype-faces-up-to-standard-simplex n n

∂Δ : ℕ → UU I1
∂Δ = type-subtype ∘ subtype-boundary-standard-simplex

-- TODO: add alternative definition
```

### The boundary of the standard simplex is included in the standard simplex

```text
leq-subtype-auxillary-face-standard-simplex-standard-simplex :
  (n r : ℕ) →
  subtype-auxillary-face-standard-simplex n r ⊆ subtype-Δ n
leq-subtype-auxillary-face-standard-simplex-standard-simplex 1 0 _ _ =
  raise-star
leq-subtype-auxillary-face-standard-simplex-standard-simplex 2 0 (x , y) =
  leq-inv-eq-Δ¹
leq-subtype-auxillary-face-standard-simplex-standard-simplex 2 1 _ =
  min-leq-eq-Δ¹
leq-subtype-auxillary-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) 0 _ (x=y , d) =
  ( leq-inv-eq-Δ¹ x=y , d)
leq-subtype-auxillary-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) (_ , u) (x≥y , f) =
  ( x≥y ,
    leq-subtype-auxillary-face-standard-simplex-standard-simplex
      ( succ-ℕ (succ-ℕ n)) r u f)

leq-subtype-face-standard-simplex-standard-simplex :
  (n r : ℕ) → subtype-face-standard-simplex n r ⊆ subtype-Δ n
leq-subtype-face-standard-simplex-standard-simplex 1 0 _ _ =
  raise-star
leq-subtype-face-standard-simplex-standard-simplex 1 (succ-ℕ r) _ _ =
  raise-star
leq-subtype-face-standard-simplex-standard-simplex 2 0 _ =
  max-leq-eq-Δ¹ ∘ inv
leq-subtype-face-standard-simplex-standard-simplex 2 (succ-ℕ r) =
  leq-subtype-auxillary-face-standard-simplex-standard-simplex 2 r
leq-subtype-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) 0 _ (1=x , p) =
  ( max-leq-eq-Δ¹ (inv 1=x) , p)
leq-subtype-face-standard-simplex-standard-simplex
  ( succ-ℕ (succ-ℕ (succ-ℕ n))) (succ-ℕ r) =
  leq-subtype-auxillary-face-standard-simplex-standard-simplex
    ( succ-ℕ (succ-ℕ (succ-ℕ n)))
    ( r)

leq-subtype-faces-up-to-standard-simplex-standard-simplex :
  (n k : ℕ) →
  subtype-faces-up-to-standard-simplex n k ⊆ subtype-Δ n
leq-subtype-faces-up-to-standard-simplex-standard-simplex n 0 =
  leq-subtype-face-standard-simplex-standard-simplex n 0
leq-subtype-faces-up-to-standard-simplex-standard-simplex n (succ-ℕ k) x =
  elim-disjunction
    ( subtype-Δ n x)
    ( leq-subtype-face-standard-simplex-standard-simplex n (succ-ℕ k) x)
    ( leq-subtype-faces-up-to-standard-simplex-standard-simplex n k x)

leq-subtype-boundary-standard-simplex-standard-simplex :
  (n : ℕ) → subtype-boundary-standard-simplex n ⊆ subtype-Δ n
leq-subtype-boundary-standard-simplex-standard-simplex n =
  leq-subtype-faces-up-to-standard-simplex-standard-simplex n n

inclusion-boundary-standard-simplex : (n : ℕ) → ∂Δ n → Δ n
inclusion-boundary-standard-simplex n =
  tot (leq-subtype-boundary-standard-simplex-standard-simplex n)
```
