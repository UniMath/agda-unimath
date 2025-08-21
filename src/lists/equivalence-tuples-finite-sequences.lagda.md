# The equivalence between tuples and finite sequences

```agda
module lists.equivalence-tuples-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.tuples
```

</details>

### Tuples on a type are equivalent to finite sequences in it

```agda
module _
  {l : Level} {A : UU l}
  where

  tuple-fin-sequence : (n : ℕ) → fin-sequence A n → tuple A n
  tuple-fin-sequence zero-ℕ v = empty-tuple
  tuple-fin-sequence (succ-ℕ n) v =
    head-fin-sequence n v ∷
    tuple-fin-sequence n (tail-fin-sequence n v)

  fin-sequence-tuple : (n : ℕ) → tuple A n → fin-sequence A n
  fin-sequence-tuple zero-ℕ v = empty-fin-sequence
  fin-sequence-tuple (succ-ℕ n) (a ∷ v) =
    cons-fin-sequence n a (fin-sequence-tuple n v)

  is-section-fin-sequence-tuple :
    (n : ℕ) → (tuple-fin-sequence n ∘ fin-sequence-tuple n) ~ id
  is-section-fin-sequence-tuple .zero-ℕ empty-tuple = refl
  is-section-fin-sequence-tuple .(succ-ℕ _) (a ∷ v) =
    ap (λ u → a ∷ u) (is-section-fin-sequence-tuple _ v)

  abstract
    is-retraction-fin-sequence-tuple :
      (n : ℕ) →
      (fin-sequence-tuple n ∘ tuple-fin-sequence n) ~ id
    is-retraction-fin-sequence-tuple zero-ℕ v = eq-htpy (λ ())
    is-retraction-fin-sequence-tuple (succ-ℕ n) v =
      eq-htpy
        ( λ where
          ( inl x) →
            htpy-eq
              ( is-retraction-fin-sequence-tuple
                ( n)
                ( tail-fin-sequence n v))
              ( x)
          ( inr star) → refl)

  is-equiv-tuple-fin-sequence :
    (n : ℕ) → is-equiv (tuple-fin-sequence n)
  is-equiv-tuple-fin-sequence n =
    is-equiv-is-invertible
      ( fin-sequence-tuple n)
      ( is-section-fin-sequence-tuple n)
      ( is-retraction-fin-sequence-tuple n)

  is-equiv-fin-sequence-tuple :
    (n : ℕ) → is-equiv (fin-sequence-tuple n)
  is-equiv-fin-sequence-tuple n =
    is-equiv-is-invertible
      ( tuple-fin-sequence n)
      ( is-retraction-fin-sequence-tuple n)
      ( is-section-fin-sequence-tuple n)

  compute-tuple : (n : ℕ) → fin-sequence A n ≃ tuple A n
  pr1 (compute-tuple n) = tuple-fin-sequence n
  pr2 (compute-tuple n) = is-equiv-tuple-fin-sequence n
```

### Characterizing the elementhood predicate

```agda
  is-in-fin-sequence-is-in-tuple :
    (n : ℕ) (v : tuple A n) (x : A) →
    (x ∈-tuple v) → (in-fin-sequence n x (fin-sequence-tuple n v))
  is-in-fin-sequence-is-in-tuple (succ-ℕ n) (y ∷ l) x (is-head .x l) =
    (inr star) , refl
  is-in-fin-sequence-is-in-tuple
    (succ-ℕ n) (y ∷ l) x (is-in-tail .x x₁ l I) =
    inl (pr1 (is-in-fin-sequence-is-in-tuple n l x I)) ,
    pr2 (is-in-fin-sequence-is-in-tuple n l x I)

  is-in-tuple-is-in-fin-sequence :
    (n : ℕ) (v : tuple A n) (x : A) →
    (in-fin-sequence n x (fin-sequence-tuple n v)) → (x ∈-tuple v)
  is-in-tuple-is-in-fin-sequence (succ-ℕ n) (y ∷ v) x (inl k , p) =
    is-in-tail x y v (is-in-tuple-is-in-fin-sequence n v x (k , p))
  is-in-tuple-is-in-fin-sequence (succ-ℕ n) (y ∷ v) _ (inr k , refl) =
    is-head (fin-sequence-tuple (succ-ℕ n) (y ∷ v) (inr k)) v
```
