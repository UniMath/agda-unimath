# Sums of finite sequences of elements in semigroups

```agda
module group-theory.sums-of-finite-sequences-of-elements-semigroups where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import group-theory.semigroups

open import linear-algebra.finite-sequences-in-semigroups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite sequence in a semigroup" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Semigroup}}
operation extends the binary operation on a
[semigroup](group-theory.semigroups.md) `G` to any nonempty
[finite sequence](lists.finite-sequences.md) of elements of `G`.

## Definition

```agda
sum-fin-sequence-type-Semigroup :
  {l : Level} (G : Semigroup l) (n : ℕ) →
  fin-sequence-type-Semigroup G (succ-ℕ n) → type-Semigroup G
sum-fin-sequence-type-Semigroup G zero-ℕ f = f (inr star)
sum-fin-sequence-type-Semigroup G (succ-ℕ n) f =
  mul-Semigroup G
    ( sum-fin-sequence-type-Semigroup G n (f ∘ inl-Fin (succ-ℕ n)))
    ( f (inr star))
```

## Properties

### Sums are homotopy invariant

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  htpy-sum-fin-sequence-type-Semigroup :
    (n : ℕ) → {f g : fin-sequence-type-Semigroup G (succ-ℕ n)} →
    f ~ g →
    sum-fin-sequence-type-Semigroup G n f ＝
    sum-fin-sequence-type-Semigroup G n g
  htpy-sum-fin-sequence-type-Semigroup n f~g =
    ap (sum-fin-sequence-type-Semigroup G n) (eq-htpy f~g)
```

### Splitting sums of `succ-ℕ n + succ-ℕ m` elements into a sum of `succ-ℕ n` elements and a sum of `succ-ℕ m` elements

```agda
abstract
  split-sum-fin-sequence-type-Semigroup :
    {l : Level} (G : Semigroup l)
    (n m : ℕ) (f : fin-sequence-type-Semigroup G (succ-ℕ n +ℕ succ-ℕ m)) →
    sum-fin-sequence-type-Semigroup G (succ-ℕ n +ℕ m) f ＝
    mul-Semigroup G
      ( sum-fin-sequence-type-Semigroup G n
        ( f ∘ inl-coproduct-Fin (succ-ℕ n) (succ-ℕ m)))
      ( sum-fin-sequence-type-Semigroup G m
        ( f ∘ inr-coproduct-Fin (succ-ℕ n) (succ-ℕ m)))
  split-sum-fin-sequence-type-Semigroup G n zero-ℕ f = refl
  split-sum-fin-sequence-type-Semigroup G n (succ-ℕ m) f =
    ap-mul-Semigroup G
      ( split-sum-fin-sequence-type-Semigroup G n m (f ∘ inl))
      ( refl) ∙
    associative-mul-Semigroup G _ _ _
```
