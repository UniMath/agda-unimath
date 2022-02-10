# Counting the elements of coproduct types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-coproduct-types where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)
open import elementary-number-theory.equivalences-standard-finite-types using
  ( coprod-Fin)

open import foundation.coproduct-types using
  ( coprod; inl; inr; is-left-Prop; is-right-Prop; equiv-left-summand;
    equiv-right-summand)
open import foundation.decidable-types using
  ( is-decidable-is-left; is-decidable-is-right)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv; _≃_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.identity-types using (Id; refl)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; count-unit; count-empty; count-equiv)
open import univalent-combinatorics.counting-decidable-subtypes using
  ( count-decidable-subtype)
```

## Idea

A coproduct `X + Y` has a count if and only if both `X` and `Y` have a count

## Properties

### Types equipped with a count are closed under coproducts

```agda
count-coprod :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  count X → count Y → count (coprod X Y)
pr1 (count-coprod (pair k e) (pair l f)) = add-ℕ k l
pr2 (count-coprod (pair k e) (pair l f)) =
  (equiv-coprod e f) ∘e (inv-equiv (coprod-Fin k l))

abstract
  number-of-elements-count-coprod :
    {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : count X) (f : count Y) →
    Id ( number-of-elements-count (count-coprod e f))
      ( add-ℕ (number-of-elements-count e) (number-of-elements-count f))
  number-of-elements-count-coprod (pair k e) (pair l f) = refl
```

### If `X + Y` has a count, then both `X` and `Y` have a count

```agda
count-left-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count X
count-left-summand e =
  count-equiv
    ( equiv-left-summand)
    ( count-decidable-subtype is-left-Prop is-decidable-is-left e)

count-right-summand :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} → count (coprod X Y) → count Y
count-right-summand e =
  count-equiv
    ( equiv-right-summand)
    ( count-decidable-subtype is-right-Prop is-decidable-is-right e)
```
