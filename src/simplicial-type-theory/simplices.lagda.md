# Simplices

```agda
module simplicial-type-theory.simplices where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.identity-types
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

  Δ : ℕ → UU l1
  last : (n : ℕ) → Δ (n +ℕ 1) → type-Bounded-Total-Order I
  initial : (n : ℕ) → Δ (n +ℕ 2) → Δ (n +ℕ 1)

  Δ zero-ℕ = raise-unit l1
  Δ (succ-ℕ zero-ℕ) = type-Bounded-Total-Order I
  Δ (succ-ℕ (succ-ℕ n)) =
    type-subtype
      ( λ ((x , j) : Δ (succ-ℕ n) × type-Bounded-Total-Order I) →
        leq-prop-Bounded-Total-Order I j (last n x))

  last zero-ℕ i = i
  last (succ-ℕ n) ((x , j) , H) = j

  initial n ((x , j) , H) = x

  eq-Δ-succ-ℕ :
    {n : ℕ} (u v : Δ (succ-ℕ (succ-ℕ n))) →
    pr1 (pr1 u) ＝ pr1 (pr1 v) → last (succ-ℕ n) u ＝ last (succ-ℕ n) v → u ＝ v
  eq-Δ-succ-ℕ {n} u v p q =
    eq-type-subtype
      ( λ ((x , j) : Δ (succ-ℕ n) × type-Bounded-Total-Order I) →
        leq-prop-Bounded-Total-Order I j (last n x))
      ( eq-pair p q)

  d00 : Δ 0 → Δ 1
  d00 (map-raise star) = top-Bounded-Total-Order I

  d01 : Δ 0 → Δ 1
  d01 (map-raise star) = bottom-Bounded-Total-Order I

  d10 : Δ 1 → Δ 2
  pr1 (pr1 (d10 i)) = top-Bounded-Total-Order I
  pr2 (pr1 (d10 i)) = i
  pr2 (d10 i) = is-top-element-top-Bounded-Total-Order I i

  d11 : Δ 1 → Δ 2
  pr1 (pr1 (d11 i)) = i
  pr2 (pr1 (d11 i)) = i
  pr2 (d11 i) = refl-leq-Bounded-Total-Order I i

  d12 : Δ 1 → Δ 2
  pr1 (pr1 (d12 i)) = i
  pr2 (pr1 (d12 i)) = bottom-Bounded-Total-Order I
  pr2 (d12 i) = is-bottom-element-bottom-Bounded-Total-Order I i

  identity-d10-d00 :
    (i : Δ 0) → d10 (d00 i) ＝ d11 (d00 i)
  identity-d10-d00 (map-raise star) =
    eq-Δ-succ-ℕ _ _ refl refl

  identity-d10-d01 :
    (i : Δ 0) → d10 (d01 i) ＝ d12 (d00 i)
  identity-d10-d01 (map-raise star) =
    eq-Δ-succ-ℕ _ _ refl refl

  identity-d11-d01 :
    (i : Δ 0) → d11 (d01 i) ＝ d12 (d01 i)
  identity-d11-d01 (map-raise star) =
    eq-Δ-succ-ℕ _ _ refl refl

  s00 : Δ 1 → Δ 0
  s00 i = map-raise star

  s10 : Δ 2 → Δ 1
  s10 ((x , j) , H) = j

  s11 : Δ 2 → Δ 1
  s11 p = initial _ p

  identity-s00-s10 :
    (p : Δ 2) → s00 (s10 p) ＝ s00 (s11 p)
  identity-s00-s10 ((_ , _) , _) = refl

```
