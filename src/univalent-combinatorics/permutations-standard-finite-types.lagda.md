# Permutations of standard finite types

```agda
module univalent-combinatorics.permutations-standard-finite-types where
```

<details><summary>Imports</summary>

```agda
open import univalent-combinatorics.standard-finite-types
open import univalent-combinatorics.equality-standard-finite-types

open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers

open import foundation.automorphisms
open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.coproduct-types
open import foundation.unit-type
open import foundation.equivalences
open import foundation.identity-types
open import foundation.negation
open import foundation.homotopies
open import foundation.functions
open import foundation.empty-types
```

## Idea

A permutation of `Fin n` is an automorphism of `Fin n`.

## Definitions

```agda
Permutation : (n : ℕ) → UU lzero
Permutation n = Aut (Fin n)
```

## Examples

### Cycle of length 2

```agda
module _
  (n : ℕ) (i j : Fin n)
  where

  map-two-cycle-permutation-helper :
    (k : Fin n) →
    (i ＝ k) + (¬ (i ＝ k)) → (j ＝ k) + (¬ (j ＝ k)) → Fin n
  map-two-cycle-permutation-helper k (inl _) p = j
  map-two-cycle-permutation-helper k (inr _) (inl _) = i
  map-two-cycle-permutation-helper k (inr _) (inr _) = k

  map-two-cycle-permutation :
    (k : Fin n) → Fin n
  map-two-cycle-permutation k =
    map-two-cycle-permutation-helper
      ( k)
      ( has-decidable-equality-Fin n i k)
      ( has-decidable-equality-Fin n j k)

  is-involution-map-two-cycle-permutation-helper :
    (k : Fin n) →
    (p : (i ＝ k) + (¬ (i ＝ k))) →
    (q : (j ＝ k) + (¬ (j ＝ k))) →
    (p' :
      (i ＝ (map-two-cycle-permutation-helper k p q)) +
      (¬ (i ＝ (map-two-cycle-permutation-helper k p q)))) →
    (q' :
      (j ＝ (map-two-cycle-permutation-helper k p q)) +
      (¬ (j ＝ (map-two-cycle-permutation-helper k p q)))) →
    map-two-cycle-permutation-helper
      ( map-two-cycle-permutation-helper k p q)
      ( p')
      ( q') ＝
    k
  is-involution-map-two-cycle-permutation-helper k (inl p) _ (inl p') _ =
     inv p' ∙ p
  is-involution-map-two-cycle-permutation-helper k (inl p) _ (inr _) (inl _) =
    p
  is-involution-map-two-cycle-permutation-helper k (inl _) _ (inr _) (inr q') =
    ex-falso (q' refl)
  is-involution-map-two-cycle-permutation-helper k (inr _) (inl q) (inl _) _ =
    q
  is-involution-map-two-cycle-permutation-helper k (inr _) (inl q) (inr _) (inl q') =
    inv q' ∙ q
  is-involution-map-two-cycle-permutation-helper k (inr _) (inl _) (inr p') (inr _) =
    ex-falso (p' refl)
  is-involution-map-two-cycle-permutation-helper k (inr p) (inr _) (inl p') _ =
    ex-falso (p p')
  is-involution-map-two-cycle-permutation-helper k (inr _) (inr q) (inr _) (inl q') =
    ex-falso (q q')
  is-involution-map-two-cycle-permutation-helper k (inr _) (inr _) (inr _) (inr _) =
    refl

  is-involution-map-two-cycle-permutation :
    (map-two-cycle-permutation ∘ map-two-cycle-permutation) ~ id
  is-involution-map-two-cycle-permutation k =
    is-involution-map-two-cycle-permutation-helper
      ( k)
      ( has-decidable-equality-Fin n _ _)
      ( has-decidable-equality-Fin n _ _)
      ( has-decidable-equality-Fin n _ _)
      ( has-decidable-equality-Fin n _ _)

  two-cycle-permutation : Permutation n
  pr1 two-cycle-permutation = map-two-cycle-permutation
  pr2 two-cycle-permutation =
    is-equiv-has-inverse
      map-two-cycle-permutation
      is-involution-map-two-cycle-permutation
      is-involution-map-two-cycle-permutation
```

### Swap the two last element of `Fin n`

```agda
module _
  (n : ℕ)
  where

  map-swap-two-last-elements-permutation :
    Fin (succ-ℕ (succ-ℕ n)) → Fin (succ-ℕ (succ-ℕ n))
  map-swap-two-last-elements-permutation (inl (inl x)) = inl (inl x)
  map-swap-two-last-elements-permutation (inl (inr star)) = inr star
  map-swap-two-last-elements-permutation (inr star) = inl (inr star)

  is-involution-map-swap-two-last-elements-permutation :
    ( map-swap-two-last-elements-permutation ∘
      map-swap-two-last-elements-permutation) ~
    id
  is-involution-map-swap-two-last-elements-permutation (inl (inl x)) = refl
  is-involution-map-swap-two-last-elements-permutation (inl (inr star)) = refl
  is-involution-map-swap-two-last-elements-permutation (inr star) = refl

  swap-two-last-elements-permutation : Permutation (succ-ℕ (succ-ℕ n))
  pr1 swap-two-last-elements-permutation = map-swap-two-last-elements-permutation
  pr2 swap-two-last-elements-permutation =
    is-equiv-has-inverse
      map-swap-two-last-elements-permutation
      is-involution-map-swap-two-last-elements-permutation
      is-involution-map-swap-two-last-elements-permutation
```
