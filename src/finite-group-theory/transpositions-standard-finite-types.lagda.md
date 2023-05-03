# Transpositions of standard finite types

```agda
module finite-group-theory.transpositions-standard-finite-types where
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

open import finite-group-theory.permutations-standard-finite-types
```

## Idea

Given `i` and `j` in `Fin n`, the transposition associated to `i` and `j` swap
these two elements.

## Definition

### Transposition

```agda
module _
  (n : ℕ) (i j : Fin n)
  where

  helper-map-transposition-Fin :
    (k : Fin n) →
    (i ＝ k) + (¬ (i ＝ k)) → (j ＝ k) + (¬ (j ＝ k)) → Fin n
  helper-map-transposition-Fin k (inl _) p = j
  helper-map-transposition-Fin k (inr _) (inl _) = i
  helper-map-transposition-Fin k (inr _) (inr _) = k

  map-transposition-Fin :
    (k : Fin n) → Fin n
  map-transposition-Fin k =
    helper-map-transposition-Fin
      ( k)
      ( has-decidable-equality-Fin n i k)
      ( has-decidable-equality-Fin n j k)

  helper-is-involution-map-transposition-Fin :
    (k : Fin n) →
    (p : (i ＝ k) + (¬ (i ＝ k))) →
    (q : (j ＝ k) + (¬ (j ＝ k))) →
    (p' :
      (i ＝ (helper-map-transposition-Fin k p q)) +
      (¬ (i ＝ (helper-map-transposition-Fin k p q)))) →
    (q' :
      (j ＝ (helper-map-transposition-Fin k p q)) +
      (¬ (j ＝ (helper-map-transposition-Fin k p q)))) →
    helper-map-transposition-Fin
      ( helper-map-transposition-Fin k p q)
      ( p')
      ( q') ＝
    k
  helper-is-involution-map-transposition-Fin k (inl p) _ (inl p') _ =
     inv p' ∙ p
  helper-is-involution-map-transposition-Fin k (inl p) _ (inr _) (inl _) =
    p
  helper-is-involution-map-transposition-Fin k (inl _) _ (inr _) (inr q') =
    ex-falso (q' refl)
  helper-is-involution-map-transposition-Fin k (inr _) (inl q) (inl _) _ =
    q
  helper-is-involution-map-transposition-Fin k (inr _) (inl q) (inr _) (inl q') =
    inv q' ∙ q
  helper-is-involution-map-transposition-Fin k (inr _) (inl _) (inr p') (inr _) =
    ex-falso (p' refl)
  helper-is-involution-map-transposition-Fin k (inr p) (inr _) (inl p') _ =
    ex-falso (p p')
  helper-is-involution-map-transposition-Fin k (inr _) (inr q) (inr _) (inl q') =
    ex-falso (q q')
  helper-is-involution-map-transposition-Fin k (inr _) (inr _) (inr _) (inr _) =
    refl

  is-involution-map-transposition-Fin :
    (map-transposition-Fin ∘ map-transposition-Fin) ~ id
  is-involution-map-transposition-Fin k =
    helper-is-involution-map-transposition-Fin
      ( k)
      ( has-decidable-equality-Fin n _ _)
      ( has-decidable-equality-Fin n _ _)
      ( has-decidable-equality-Fin n _ _)
      ( has-decidable-equality-Fin n _ _)

  transposition-Fin : Permutation n
  pr1 transposition-Fin = map-transposition-Fin
  pr2 transposition-Fin =
    is-equiv-has-inverse
      map-transposition-Fin
      is-involution-map-transposition-Fin
      is-involution-map-transposition-Fin
```

### The transposition which swap the two last element of `Fin n`

```agda
module _
  (n : ℕ)
  where

  map-swap-two-last-elements-transposition-Fin :
    Fin (succ-ℕ (succ-ℕ n)) → Fin (succ-ℕ (succ-ℕ n))
  map-swap-two-last-elements-transposition-Fin (inl (inl x)) = inl (inl x)
  map-swap-two-last-elements-transposition-Fin (inl (inr star)) = inr star
  map-swap-two-last-elements-transposition-Fin (inr star) = inl (inr star)

  is-involution-map-swap-two-last-elements-transposition-Fin :
    ( map-swap-two-last-elements-transposition-Fin ∘
      map-swap-two-last-elements-transposition-Fin) ~
    id
  is-involution-map-swap-two-last-elements-transposition-Fin (inl (inl x)) =
    refl
  is-involution-map-swap-two-last-elements-transposition-Fin (inl (inr star)) =
    refl
  is-involution-map-swap-two-last-elements-transposition-Fin (inr star) = refl

  swap-two-last-elements-transposition-Fin : Permutation (succ-ℕ (succ-ℕ n))
  pr1 swap-two-last-elements-transposition-Fin =
    map-swap-two-last-elements-transposition-Fin
  pr2 swap-two-last-elements-transposition-Fin =
    is-equiv-has-inverse
      map-swap-two-last-elements-transposition-Fin
      is-involution-map-swap-two-last-elements-transposition-Fin
      is-involution-map-swap-two-last-elements-transposition-Fin
```
