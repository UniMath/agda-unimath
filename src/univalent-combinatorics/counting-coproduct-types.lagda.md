# Counting the elements of coproduct types

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.counting-coproduct-types where

open import elementary-number-theory.addition-natural-numbers using (add-ℕ)

open import foundation.coproduct-types using
  ( coprod; inl; inr; is-left-Prop; is-right-Prop; equiv-left-summand;
    equiv-right-summand)
open import foundation.decidable-types using
  ( is-decidable-is-left; is-decidable-is-right)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_∘e_; inv-equiv; _≃_)
open import foundation.functoriality-coproduct-types using (equiv-coprod)
open import foundation.identity-types using (Id; refl; _∙_; inv)
open import foundation.universe-levels using (Level; UU; lzero)

open import univalent-combinatorics.counting using
  ( count; number-of-elements-count; count-unit; count-empty; count-equiv)
open import univalent-combinatorics.counting-decidable-subtypes using
  ( count-decidable-subtype)
open import univalent-combinatorics.double-counting using (double-counting)
open import univalent-combinatorics.equivalences-standard-finite-types using
  ( coprod-Fin)
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

### If each of `A`, `B`, and `A + B` come equipped with countings, then the number of elements of `A` and of `B` add up to the number of elements of `A + B`

```agda
abstract
  double-counting-coprod :
    { l1 l2 : Level} {A : UU l1} {B : UU l2}
    ( count-A : count A) (count-B : count B) (count-C : count (coprod A B)) →
    Id ( number-of-elements-count count-C)
       ( add-ℕ
         ( number-of-elements-count count-A)
         ( number-of-elements-count count-B))
  double-counting-coprod count-A count-B count-C =
    ( double-counting count-C (count-coprod count-A count-B)) ∙
    ( number-of-elements-count-coprod count-A count-B)

abstract
  sum-number-of-elements-coprod :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} (e : count (coprod A B)) →
    Id ( add-ℕ ( number-of-elements-count (count-left-summand e))
               ( number-of-elements-count (count-right-summand e)))
       ( number-of-elements-count e)
  sum-number-of-elements-coprod e =
    ( inv
      ( number-of-elements-count-coprod
        ( count-left-summand e)
        ( count-right-summand e))) ∙
    ( inv
      ( double-counting-coprod
        ( count-left-summand e)
        ( count-right-summand e) e))
```
