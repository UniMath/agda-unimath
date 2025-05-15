# Sums of counted families of elements in commutative monoids

```agda
{-# OPTIONS --lossy-unification #-}

module group-theory.sums-of-counted-families-in-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.sums-of-finite-sequences-in-commutative-monoids

open import lists.lists

open import univalent-combinatorics.counting
open import univalent-combinatorics.counting-dependent-pair-types
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.double-counting
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sum operation extends the binary operation on a
[commutative monoid](group-theory.commutative-monoids.md) `M` to any
family of elements of `M` indexed by a
[counted](univalent-combinatorics.counting.md) type.

## Definition

```agda
sum-count-Commutative-Monoid :
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2) →
  count A → (A → type-Commutative-Monoid M) → type-Commutative-Monoid M
sum-count-Commutative-Monoid M A (n , Fin-n≃A) f =
  sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv Fin-n≃A)
```

## Properties

### Sums for a counted type are homotopy invariant

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  htpy-sum-count-Commutative-Monoid :
    (c : count A) →
    {f g : A → type-Commutative-Monoid M} → (f ~ g) →
    sum-count-Commutative-Monoid M A c f ＝
    sum-count-Commutative-Monoid M A c g
  htpy-sum-count-Commutative-Monoid (nA , _) H =
    htpy-sum-fin-sequence-type-Commutative-Monoid M nA (λ i → H _)
```

### Two counts for the same type produce equal sums

```agda
module _
  {l1 l2 : Level} (M : Commutative-Monoid l1) (A : UU l2)
  where

  abstract
    eq-sum-count-equiv-Commutative-Monoid :
      (n : ℕ) → (equiv1 equiv2 : Fin n ≃ A) →
      (f : A → type-Commutative-Monoid M) →
      sum-count-Commutative-Monoid M A (n , equiv1) f ＝
      sum-count-Commutative-Monoid M A (n , equiv2) f
    eq-sum-count-equiv-Commutative-Monoid n equiv1 equiv2 f =
      equational-reasoning
      sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv equiv1)
      ＝
        sum-fin-sequence-type-Commutative-Monoid
          ( M)
          ( n)
          ( (f ∘ map-equiv equiv1) ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2))
        by
          preserves-sum-permutation-Commutative-Monoid
            ( M)
            ( n)
            ( inv-equiv equiv1 ∘e equiv2)
            ( f ∘ map-equiv equiv1)
      ＝ sum-fin-sequence-type-Commutative-Monoid M n (f ∘ map-equiv equiv2)
        by
          ap
            ( λ g →
              sum-fin-sequence-type-Commutative-Monoid
                ( M)
                ( n)
                ( f ∘ (g ∘ map-equiv equiv2)))
            ( eq-htpy (is-section-map-inv-equiv equiv1))

    eq-sum-count-Commutative-Monoid :
      (f : A → type-Commutative-Monoid M) (c1 c2 : count A) →
      sum-count-Commutative-Monoid M A c1 f ＝
      sum-count-Commutative-Monoid M A c2 f
    eq-sum-count-Commutative-Monoid f c1@(n , e1) c2@(_ , e2)
      with double-counting c1 c2
    ... | refl = eq-sum-count-equiv-Commutative-Monoid n e1 e2 f
```

### Sums of counted families indexed by equivalent types are equal

```agda
module _
  {l1 l2 l3 : Level} (M : Commutative-Monoid l1)
  (A : UU l2) (B : UU l3) (H : A ≃ B)
  where

  abstract
    sum-equiv-count-Commutative-Monoid :
      (cA : count A) (cB : count B) (f : A → type-Commutative-Monoid M) →
      sum-count-Commutative-Monoid M A cA f ＝
      sum-count-Commutative-Monoid M B cB (f ∘ map-inv-equiv H)
    sum-equiv-count-Commutative-Monoid
      cA@(nA , Fin-nA≃A) cB@(_ , Fin-nB≃B) f
      with double-counting-equiv cA cB H
    ... | refl =
      preserves-sum-permutation-Commutative-Monoid
        ( M)
        ( nA)
        ( inv-equiv Fin-nA≃A ∘e inv-equiv H ∘e Fin-nB≃B)
        ( _) ∙
      htpy-sum-fin-sequence-type-Commutative-Monoid
        ( M)
        ( nA)
        ( λ i → ap f (is-section-map-inv-equiv Fin-nA≃A _))
```
