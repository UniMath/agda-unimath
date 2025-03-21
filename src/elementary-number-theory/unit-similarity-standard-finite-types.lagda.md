# Unit similarity on the standard finite types

```agda
module elementary-number-theory.unit-similarity-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.congruence-natural-numbers
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.unit-elements-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.universe-levels

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Two elements `x y : Fin k` are said to be unit similar if there is a unit
element `u : Fin k` such that `mul-Fin u x = y`. This relation gives a groupoid
structure on `Fin k`.

## Definition

### Unit similarity in `Fin k`

```agda
sim-unit-Fin :
  (k : ℕ) → Fin k → Fin k → UU lzero
sim-unit-Fin k x y = Σ (unit-Fin k) (λ u → mul-Fin k (pr1 u) x ＝ y)
```

### Unit similarity on `ℕ`

```agda
sim-unit-ℕ :
  (k : ℕ) → ℕ → ℕ → UU lzero
sim-unit-ℕ k x y =
  Σ (Σ ℕ (λ l → cong-ℕ k l 1)) (λ l → cong-ℕ k ((pr1 l) *ℕ x) y)
```

### Congruence to `1`

```agda
sim-unit-one-ℕ : (k x : ℕ) → UU lzero
sim-unit-one-ℕ k x = Σ ℕ (λ l → cong-ℕ k (l *ℕ x) 1)
```

## Properties

### Unit similarity is an equivalence relation

```agda
refl-sim-unit-Fin : {k : ℕ} → is-reflexive (sim-unit-Fin k)
pr1 (refl-sim-unit-Fin {succ-ℕ k} x) = one-unit-Fin
pr2 (refl-sim-unit-Fin {succ-ℕ k} x) = left-unit-law-mul-Fin k x

symmetric-sim-unit-Fin : {k : ℕ} → is-symmetric (sim-unit-Fin k)
pr1 (symmetric-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  inv-unit-Fin (pair u (pair v q))
pr2 (symmetric-sim-unit-Fin {succ-ℕ k} x y (pair (pair u (pair v q)) p)) =
  ( ( ( ap (mul-Fin (succ-ℕ k) v) (inv p)) ∙
        ( inv (associative-mul-Fin (succ-ℕ k) v u x))) ∙
      ( ap (mul-Fin' (succ-ℕ k) x) q)) ∙
    ( left-unit-law-mul-Fin k x)

transitive-sim-unit-Fin : {k : ℕ} → is-transitive (sim-unit-Fin k)
pr1 (transitive-sim-unit-Fin {succ-ℕ k} x y z (pair v q) (pair u p)) =
  mul-unit-Fin (succ-ℕ k) v u
pr2 (transitive-sim-unit-Fin {succ-ℕ k} x y z (pair v q) (pair u p)) =
  ( associative-mul-Fin (succ-ℕ k) (pr1 v) (pr1 u) x) ∙
  ( ap (mul-Fin (succ-ℕ k) (pr1 v)) p ∙ q)
```

### A natural number `x` is congruent to `1` modulo `k+1` if and only if `[x]_{k+1}` is unit similar to `1`

```agda
is-unit-similar-one-sim-unit-mod-succ-ℕ :
  (k x : ℕ) → sim-unit-Fin (succ-ℕ k) (mod-succ-ℕ k x) (one-Fin k) →
  sim-unit-one-ℕ (succ-ℕ k) x
pr1 (is-unit-similar-one-sim-unit-mod-succ-ℕ k x (pair u p)) =
  nat-Fin (succ-ℕ k) (pr1 u)
pr2 (is-unit-similar-one-sim-unit-mod-succ-ℕ k x (pair u p)) =
  cong-eq-mod-succ-ℕ k
    ( (nat-Fin (succ-ℕ k) (pr1 u)) *ℕ x)
    ( 1)
    ( ( eq-mod-succ-cong-ℕ k
        ( (nat-Fin (succ-ℕ k) (pr1 u)) *ℕ x)
        ( (nat-Fin (succ-ℕ k) (pr1 u)) *ℕ (nat-Fin (succ-ℕ k) (mod-succ-ℕ k x)))
        ( scalar-invariant-cong-ℕ
          ( succ-ℕ k)
          ( x)
          ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
          ( nat-Fin (succ-ℕ k) (pr1 u))
          ( symmetric-cong-ℕ
            ( succ-ℕ k)
            ( nat-Fin (succ-ℕ k) (mod-succ-ℕ k x))
            ( x)
            ( cong-nat-mod-succ-ℕ k x)))) ∙
      ( p))
```
