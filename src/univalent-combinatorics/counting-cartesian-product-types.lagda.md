# Counting the elements in cartesian product types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-cartesian-product-types where

open import elementary-number-theory.equivalences-standard-finite-types using
  ( prod-Fin)
open import elementary-number-theory.multiplication-natural-numbers using
  ( mul-ℕ)

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( equiv-is-contr; is-contr-total-path')
open import foundation.decidable-equality using
  ( has-decidable-equality-right-factor)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv; _≃_)
open import foundation.functoriality-cartesian-product-types using
  ( equiv-prod)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.identity-types using (Id; refl)
open import foundation.type-arithmetic-cartesian-product-types using
  ( commutative-prod)
open import foundation.type-arithmetic-dependent-pair-types using (assoc-Σ)
open import foundation.type-arithmetic-unit-type using (right-unit-law-prod)
open import foundation.unit-type using (is-contr-unit)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; count-equiv; has-decidable-equality-count)
open import univalent-combinatorics.counting-decidable-subtypes using
  ( count-eq)
open import univalent-combinatorics.counting-dependent-pair-types using
  ( count-Σ)
```

```agda
-- Corollary 16.1.8

count-prod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count X → count Y → count (X × Y)
pr1 (count-prod (pair k e) (pair l f)) = mul-ℕ k l
pr2 (count-prod (pair k e) (pair l f)) =
  (equiv-prod e f) ∘e (inv-equiv (prod-Fin k l))

abstract
  number-of-elements-count-prod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (count-A : count A)
    (count-B : count B) →
    Id ( number-of-elements-count
         ( count-prod count-A count-B))
       ( mul-ℕ
         ( number-of-elements-count count-A)
         ( number-of-elements-count count-B))
  number-of-elements-count-prod (pair k e) (pair l f) = refl

equiv-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (y : Y) →
  (Σ (X × Y) (λ t → Id (pr2 t) y)) ≃ X
equiv-left-factor {l1} {l2} {X} {Y} y =
  ( ( right-unit-law-prod) ∘e
    ( equiv-tot
      ( λ x → equiv-is-contr (is-contr-total-path' y) is-contr-unit))) ∘e
  ( assoc-Σ X (λ x → Y) (λ t → Id (pr2 t) y))

count-left-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → Y → count X
count-left-factor e y =
  count-equiv
    ( equiv-left-factor y)
    ( count-Σ e
      ( λ z →
        count-eq
          ( has-decidable-equality-right-factor
            ( has-decidable-equality-count e)
            ( pr1 z))
          ( pr2 z)
          ( y)))

count-right-factor :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (X × Y) → X → count Y
count-right-factor e x =
  count-left-factor (count-equiv commutative-prod e) x
```
