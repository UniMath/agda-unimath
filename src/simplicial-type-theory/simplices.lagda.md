# Simplices

```agda
module simplicial-type-theory.simplices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.bounded-total-orders
```

</details>

## Idea

Goals

Formalize

- is-segal
- comp-is-segal
- witness-comp-is-segal
- uniqueness-comp-is-segal
- is-local-horn-inclusion
- The equivalence between is-local-horn-inclusion and is-segal
- is-local-horn-inclusion-function-type
- is-segal-function-type
- trivial identities
- associativity of comp-is-segal

## Definitions

```agda
module simplex
  {l1 : Level} (I : Bounded-Total-Order l1 l1)
  where

  mutual
  
    data
      Δ : ℕ → UU l1
      where
      
      pt-Δ : Δ 0

      cons-Δ :
        {n : ℕ} (x : Δ n) (i : type-Bounded-Total-Order I) →
        (H : leq-Bounded-Total-Order I i (final-Δ n x)) → Δ (succ-ℕ n)

    final-Δ : (n : ℕ) → Δ n → type-Bounded-Total-Order I
    final-Δ n pt-Δ = top-Bounded-Total-Order I
    final-Δ _ (cons-Δ x i H) = i

  ap-cons-Δ :
    {n : ℕ} {x y : Δ n} (p : x ＝ y)
    {i j : type-Bounded-Total-Order I} (q : i ＝ j) →
    (H : leq-Bounded-Total-Order I i (final-Δ n x)) →
    (K : leq-Bounded-Total-Order I j (final-Δ n y)) →
    cons-Δ x i H ＝ cons-Δ y j K
  ap-cons-Δ refl refl H K =
    ap (cons-Δ _ _) (eq-is-prop (is-prop-leq-Bounded-Total-Order I _ _))

  initial-Δ : (n : ℕ) → Δ (n +ℕ 1) → Δ n
  initial-Δ n (cons-Δ x i H) = x
    
  data
    Eq-Δ : (n : ℕ) → Δ n → Δ n → UU l1
    where

    refl-Eq-pt-Δ : Eq-Δ 0 pt-Δ pt-Δ

    Eq-cons-Δ :
      {n : ℕ} {x y : Δ n} {i j : type-Bounded-Total-Order I} →
      (H : leq-Bounded-Total-Order I i (final-Δ n x)) →
      (K : leq-Bounded-Total-Order I j (final-Δ n y)) →
      Eq-Δ n x y → i ＝ j → Eq-Δ (succ-ℕ n) (cons-Δ x i H) (cons-Δ y j K)

  refl-Eq-Δ :
    {n : ℕ} → is-reflexive (Eq-Δ n)
  refl-Eq-Δ pt-Δ = refl-Eq-pt-Δ
  refl-Eq-Δ (cons-Δ x i H) =
    Eq-cons-Δ H H (refl-Eq-Δ x) refl

  Eq-eq-Δ :
    (n : ℕ) (x y : Δ n) → x ＝ y → Eq-Δ n x y
  Eq-eq-Δ n x y refl = refl-Eq-Δ x

  eq-Eq-Δ :
    {n : ℕ} {x y : Δ n} → Eq-Δ n x y → x ＝ y
  eq-Eq-Δ refl-Eq-pt-Δ = refl
  eq-Eq-Δ (Eq-cons-Δ H K e refl) =
    ap-cons-Δ (eq-Eq-Δ e) refl H K

  in-Δ : type-Bounded-Total-Order I → Δ 1
  in-Δ i = cons-Δ pt-Δ i (is-top-element-top-Bounded-Total-Order I _)

  d00 : Δ 0 → Δ 1
  d00 pt-Δ = in-Δ (top-Bounded-Total-Order I)

  d01 : Δ 0 → Δ 1
  d01 pt-Δ = in-Δ (bottom-Bounded-Total-Order I)

  d10 : Δ 1 → Δ 2
  d10 (cons-Δ pt-Δ i H) =
    cons-Δ (d00 pt-Δ) i H

  d11 : Δ 1 → Δ 2
  d11 x = cons-Δ x (final-Δ 1 x) (refl-leq-Bounded-Total-Order I _)

  d12 : Δ 1 → Δ 2
  d12 x =
    cons-Δ x
      ( bottom-Bounded-Total-Order I)
      ( is-bottom-element-bottom-Bounded-Total-Order I _)

  identity-d10-d00 :
    (i : Δ 0) → d10 (d00 i) ＝ d11 (d00 i)
  identity-d10-d00 pt-Δ =
    eq-Eq-Δ (Eq-cons-Δ _ _ (refl-Eq-Δ _) refl)

  identity-d10-d01 :
    (i : Δ 0) → d10 (d01 i) ＝ d12 (d00 i)
  identity-d10-d01 pt-Δ =
    eq-Eq-Δ (Eq-cons-Δ _ _ (refl-Eq-Δ _) refl)

  identity-d11-d01 :
    (i : Δ 0) → d11 (d01 i) ＝ d12 (d01 i)
  identity-d11-d01 pt-Δ =
    eq-Eq-Δ (Eq-cons-Δ _ _ (refl-Eq-Δ _) refl)

  s00 : Δ 1 → Δ 0
  s00 i = pt-Δ

  s10 : Δ 2 → Δ 1
  s10 (cons-Δ x i H) = in-Δ i

  s11 : Δ 2 → Δ 1
  s11 x = initial-Δ _ x

  identity-s00-s10 :
    (x : Δ 2) → s00 (s10 x) ＝ s00 (s11 x)
  identity-s00-s10 (cons-Δ x i H) = refl
```
