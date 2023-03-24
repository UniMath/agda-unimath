# Vectors of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.vectors-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-products-set-quotients
open import foundation.coproduct-types
open import foundation.equality-cartesian-product-types
open import foundation.equational-reasoning
open import foundation.equivalence-classes
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.multivariable-operations
open import foundation.raising-universe-levels
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.unit-type

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.universe-levels

open import linear-algebra.vectors

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Say we have a family of types `A1`, ..., `An` each equipped with an equivalence
relation `Ri`. Then, the set quotient of a vector with these types is the vector
of the set quotients of each `Ai`.

## Definition

### The induced relation on the vector of types

```agda
all-sim-Eq-Rel :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  ( Eq-Rel l2 (multivariable-input n A))
all-sim-Eq-Rel {l1} {l2} zero-ℕ A R = always-holds-Eq-Rel l2 (raise-unit l1)
all-sim-Eq-Rel (succ-ℕ n) A R =
  prod-Eq-Rel (R (inr star))
    ( all-sim-Eq-Rel n
      ( tail-functional-vec n A)
      ( λ x → R (inl x)))
```

### The set quotient of a vector of types

```agda
set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  UU (l1 ⊔ l2)
set-quotient-vector zero-ℕ A R = raise-unit _
set-quotient-vector (succ-ℕ n) A R =
  ( set-quotient (R (inr star))) ×
  ( set-quotient-vector n
    ( tail-functional-vec n A)
    ( λ x → R (inl x)))

is-set-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  is-set (set-quotient-vector n A R)
is-set-set-quotient-vector zero-ℕ A R = is-set-raise-unit
is-set-set-quotient-vector (succ-ℕ n) A R =
  is-set-prod
  ( is-set-set-quotient (R (inr star)))
  ( is-set-set-quotient-vector n
    ( tail-functional-vec n A)
    ( λ x → R (inl x)))

set-quotient-vector-Set :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  Set (l1 ⊔ l2)
pr1 (set-quotient-vector-Set n A R) =
  set-quotient-vector n A R
pr2 (set-quotient-vector-Set n A R) =
  is-set-set-quotient-vector n A R

quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  multivariable-input n A →
  set-quotient-vector n A R
quotient-vector-map zero-ℕ A R a = raise-star
pr1 (quotient-vector-map (succ-ℕ n) A R (a0 , a)) =
  quotient-map (R (inr star)) (a0)
pr2 (quotient-vector-map (succ-ℕ n) A R a) =
  quotient-vector-map n
    ( tail-functional-vec n A)
    ( λ x → R (inl x))
    ( tail-multivariable-input n A a)

reflects-quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  reflects-Eq-Rel (all-sim-Eq-Rel n A R) (quotient-vector-map n A R)
reflects-quotient-vector-map zero-ℕ A R p = refl
reflects-quotient-vector-map (succ-ℕ n) A R (p , p') =
  eq-pair
    ( apply-effectiveness-quotient-map' (R (inr star)) p)
    ( reflects-quotient-vector-map n
      ( tail-functional-vec n A)
      ( λ x → R (inl x)) p')

reflecting-map-quotient-vector-map :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  reflecting-map-Eq-Rel
    ( all-sim-Eq-Rel n A R)
    ( set-quotient-vector n A R)
pr1 (reflecting-map-quotient-vector-map n A R) =
  quotient-vector-map n A R
pr2 (reflecting-map-quotient-vector-map n A R) =
  reflects-quotient-vector-map n A R

equiv-set-quotient-vector :
  { l1 l2 : Level}
  ( n : ℕ)
  ( A : functional-vec (UU l1) n)
  ( R : (i : Fin n) → Eq-Rel l2 (A i)) →
  set-quotient-vector n A R ≃ set-quotient (all-sim-Eq-Rel n A R)
pr1 (equiv-set-quotient-vector zero-ℕ A R) _ = quotient-map _ raise-star
pr1 (pr1 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = raise-star
pr2 (pr1 (pr2 (equiv-set-quotient-vector {l1} {l2} zero-ℕ A R))) =
  induction-set-quotient
    ( always-holds-Eq-Rel l2 (raise-unit l1))
    ( λ x → pair _ (is-set-set-quotient _ _ x))
    ( λ x → apply-effectiveness-quotient-map' _ raise-star)
pr1 (pr2 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) _ = raise-star
pr2 (pr2 (pr2 (equiv-set-quotient-vector zero-ℕ A R))) (map-raise star) = refl
equiv-set-quotient-vector (succ-ℕ n) A R =
  equivalence-reasoning
    set-quotient (R (inr star)) ×
        ( set-quotient-vector n
          ( tail-functional-vec n A)
          ( λ x → R (inl x)))
    ≃ set-quotient (R (inr star)) ×
        ( set-quotient
          (all-sim-Eq-Rel n
          ( tail-functional-vec n A)
          ( λ x → R (inl x))))
       by lemma
    ≃ set-quotient (all-sim-Eq-Rel (succ-ℕ n) A R)
       by inv-equiv (equiv-quotient-prod-prod-set-quotient _ _)
  where
  lemma :
    ( set-quotient (R (inr star)) ×
      ( set-quotient-vector n
        ( tail-functional-vec n A)
        (λ x → R (inl x)))) ≃
      ( set-quotient (R (inr star)) ×
        ( set-quotient
          ( all-sim-Eq-Rel n
            ( tail-functional-vec n A)
            ( λ x → R (inl x)))))
  pr1 (pr1 lemma (qa0 , qa)) = qa0
  pr2 (pr1 lemma (qa0 , qa)) = map-equiv (equiv-set-quotient-vector n _ _) qa
  pr1 (pr1 (pr1 (pr2 lemma)) (qa0 , qa)) = qa0
  pr2 (pr1 (pr1 (pr2 lemma)) (qa0 , qa)) =
    map-inv-equiv (equiv-set-quotient-vector n _ _) qa
  pr2 (pr1 (pr2 lemma)) (qa0 , qa) =
    eq-pair refl (issec-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)
  pr1 (pr1 (pr2 (pr2 lemma)) (qa0 , qa)) = qa0
  pr2 (pr1 (pr2 (pr2 lemma)) (qa0 , qa)) =
    map-inv-equiv (equiv-set-quotient-vector n _ _) qa
  pr2 (pr2 (pr2 lemma)) (qa0 , qa) =
    eq-pair refl (isretr-map-inv-equiv (equiv-set-quotient-vector n _ _) qa)
```
