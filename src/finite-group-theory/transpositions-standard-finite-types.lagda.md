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
open import foundation.functoriality-coproduct-types
open import foundation.equivalence-extensionality

open import lists.lists

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions
```

## Idea

Given `i` and `j` in `Fin n`, the transposition associated to `i` and `j` swap
these two elements.

## Definitions

### Transpositions on `Fin n`

This definition uses the `standard-transposition` in [`finite-group-theory.transposition`](finite-group-theory.transposition.lagda.md)

```agda
module _
  (n : ℕ) (i j : Fin n) (neq : ¬ (i ＝ j))
  where

  transposition-Fin : Permutation n
  transposition-Fin = standard-transposition (has-decidable-equality-Fin n) neq

  map-transposition-Fin : Fin n → Fin n
  map-transposition-Fin =
    map-standard-transposition (has-decidable-equality-Fin n) neq

  left-computation-transposition-Fin :
    map-standard-transposition (has-decidable-equality-Fin n) neq i ＝ j
  left-computation-transposition-Fin =
    left-computation-standard-transposition (has-decidable-equality-Fin n) neq

  right-computation-transposition-Fin :
    map-standard-transposition (has-decidable-equality-Fin n) neq j ＝ i
  right-computation-transposition-Fin =
    right-computation-standard-transposition (has-decidable-equality-Fin n) neq

  is-fixed-point-transposition-Fin :
    (z : Fin n) →
    ¬ (i ＝ z) →
    ¬ (j ＝ z) →
    map-standard-transposition (has-decidable-equality-Fin n) neq z ＝ z
  is-fixed-point-transposition-Fin =
    is-fixed-point-standard-transposition (has-decidable-equality-Fin n) neq

-- Should I erase the following definiton ? (I think yes)
--   helper-map-transposition-Fin :
--     (k : Fin n) →
--     (i ＝ k) + (¬ (i ＝ k)) →
--     (j ＝ k) + (¬ (j ＝ k)) → Fin n
--   helper-map-transposition-Fin k (inl _) p = j
--   helper-map-transposition-Fin k (inr _) (inl _) = i
--   helper-map-transposition-Fin k (inr _) (inr _) = k

--   map-transposition-Fin' :
--     (k : Fin n) → Fin n
--   map-transposition-Fin' k =
--     helper-map-transposition-Fin
--       ( k)
--       ( has-decidable-equality-Fin n i k)
--       ( has-decidable-equality-Fin n j k)

--   helper-is-involution-map-transposition-Fin :
--     (k : Fin n) →
--     (p : (i ＝ k) + (¬ (i ＝ k))) →
--     (q : (j ＝ k) + (¬ (j ＝ k))) →
--     (p' :
--       (i ＝ (helper-map-transposition-Fin k p q)) +
--       (¬ (i ＝ (helper-map-transposition-Fin k p q)))) →
--     (q' :
--       (j ＝ (helper-map-transposition-Fin k p q)) +
--       (¬ (j ＝ (helper-map-transposition-Fin k p q)))) →
--     helper-map-transposition-Fin
--       ( helper-map-transposition-Fin k p q)
--       ( p')
--       ( q') ＝
--     k
--   helper-is-involution-map-transposition-Fin k (inl p) _ (inl p') _ =
--      inv p' ∙ p
--   helper-is-involution-map-transposition-Fin k (inl p) _ (inr _) (inl _) =
--     p
--   helper-is-involution-map-transposition-Fin k (inl _) _ (inr _) (inr q') =
--     ex-falso (q' refl)
--   helper-is-involution-map-transposition-Fin k (inr _) (inl q) (inl _) _ =
--     q
--   helper-is-involution-map-transposition-Fin
--     ( k)
--     ( inr _)
--     ( inl q)
--     ( inr _)
--     ( inl q') =
--     inv q' ∙ q
--   helper-is-involution-map-transposition-Fin
--     ( k)
--     ( inr _)
--     ( inl _)
--     ( inr p')
--     ( inr _) =
--     ex-falso (p' refl)
--   helper-is-involution-map-transposition-Fin k (inr p) (inr _) (inl p') _ =
--     ex-falso (p p')
--   helper-is-involution-map-transposition-Fin
--     ( k)
--     ( inr _)
--     ( inr q)
--     ( inr _)
--     ( inl q') =
--     ex-falso (q q')
--   helper-is-involution-map-transposition-Fin k (inr _) (inr _) (inr _) (inr _) =
--     refl

--   is-involution-map-transposition-Fin :
--     (map-transposition-Fin ∘ map-transposition-Fin) ~ id
--   is-involution-map-transposition-Fin k =
--     helper-is-involution-map-transposition-Fin
--       ( k)
--       ( has-decidable-equality-Fin n _ _)
--       ( has-decidable-equality-Fin n _ _)
--       ( has-decidable-equality-Fin n _ _)
--       ( has-decidable-equality-Fin n _ _)

--   transposition-Fin' : Permutation n
--   pr1 transposition-Fin' = map-transposition-Fin
--   pr2 transposition-Fin' =
--     is-equiv-has-inverse
--       map-transposition-Fin'
--       is-involution-map-transposition-Fin
--       is-involution-map-transposition-Fin

```

### The transposition which swap the two last element of `Fin (succ-ℕ (succ-ℕ n))`

We define directly the transposition of `Fin (succ-ℕ (succ-ℕ n))` which exchange the two elements associated to `n` and `succ-ℕ n`.

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

We show that this definiton is equivalent to the previous one.

```agda
  cases-htpy-swap-two-last-elements-transposition-Fin :
    (x : Fin (succ-ℕ (succ-ℕ n))) →
    (x ＝ neg-one-Fin (succ-ℕ n)) + (¬ (x ＝ neg-one-Fin (succ-ℕ n))) →
    (x ＝ neg-two-Fin (succ-ℕ n)) + (¬ (x ＝ neg-two-Fin (succ-ℕ n))) →
    map-swap-two-last-elements-transposition-Fin x ＝
    map-transposition-Fin
      ( succ-ℕ (succ-ℕ n))
      ( neg-one-Fin (succ-ℕ n))
      ( neg-two-Fin (succ-ℕ n))
      ( neq-inr-inl)
      ( x)
  cases-htpy-swap-two-last-elements-transposition-Fin _ (inl refl) _ =
    inv
      ( left-computation-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neq-inr-inl))
  cases-htpy-swap-two-last-elements-transposition-Fin _ (inr p) (inl refl) =
    inv
      ( right-computation-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neq-inr-inl))
  cases-htpy-swap-two-last-elements-transposition-Fin
    ( inl (inl x))
    ( inr p)
    ( inr q) =
     inv
      ( is-fixed-point-transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neq-inr-inl)
        ( inl (inl x))
        ( p ∘ inv)
        ( q ∘ inv))
  cases-htpy-swap-two-last-elements-transposition-Fin
    ( inl (inr star))
    ( inr p)
    ( inr q) = ex-falso (q refl)
  cases-htpy-swap-two-last-elements-transposition-Fin
    ( inr star)
    ( inr p)
    ( inr q) = ex-falso (p refl)

  htpy-swap-two-last-elements-transposition-Fin :
    htpy-equiv
      ( swap-two-last-elements-transposition-Fin)
      ( transposition-Fin
        ( succ-ℕ (succ-ℕ n))
        ( neg-one-Fin (succ-ℕ n))
        ( neg-two-Fin (succ-ℕ n))
        ( neq-inr-inl))
  htpy-swap-two-last-elements-transposition-Fin x =
    cases-htpy-swap-two-last-elements-transposition-Fin
      ( x)
      ( has-decidable-equality-Fin
        ( succ-ℕ (succ-ℕ n))
        ( x)
        ( neg-one-Fin (succ-ℕ n)))
      ( has-decidable-equality-Fin
        ( succ-ℕ (succ-ℕ n))
        ( x)
        ( neg-two-Fin (succ-ℕ n)))
```

### Transpositions of a pair of adjacent element in `Fin n`

```agda
adjacent-transposition-Fin :
  (n : ℕ) → (k : Fin n) → (is-nonzero-Fin n k) →
  Permutation n
adjacent-transposition-Fin 1 (inr star) neq = ex-falso (neq refl)
adjacent-transposition-Fin (succ-ℕ (succ-ℕ n)) (inl x) neq =
  equiv-coprod
    ( adjacent-transposition-Fin (succ-ℕ n) x (λ p → neq (ap inl p)))
    ( id-equiv)
adjacent-transposition-Fin (succ-ℕ (succ-ℕ n)) (inr x) neq =
  swap-two-last-elements-transposition-Fin n
```

## Properties

### Every transpositions is the composition of a list of adjacent transpositions

```agda
list-adjacent-transposition-Fin-transposition-Fin :
  (n : ℕ) → (i j : Fin n) →
  list (Σ (Fin n) (λ k → is-nonzero-Fin n k))
list-adjacent-transposition-Fin-transposition-Fin 1 (inr star) (inr star) = nil
list-adjacent-transposition-Fin-transposition-Fin
  ( succ-ℕ (succ-ℕ n))
  ( inl i)
  ( inl j) =
  {!!}
list-adjacent-transposition-Fin-transposition-Fin
  ( succ-ℕ (succ-ℕ n))
  ( inl i)
  ( inr star) =
  {!!}
list-adjacent-transposition-Fin-transposition-Fin
  ( succ-ℕ (succ-ℕ n))
  ( inr star)
  ( inl j) =
  {!!}
list-adjacent-transposition-Fin-transposition-Fin
  ( succ-ℕ (succ-ℕ n))
  ( inr star)
  ( inr star) =
  nil
```
