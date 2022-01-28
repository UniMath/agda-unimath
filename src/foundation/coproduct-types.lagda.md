# Coproduct types

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

module foundation.coproduct-types where

open import foundation.contractible-types using
  ( is-contr; eq-is-contr; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; refl)
open import foundation.injective-maps using (is-injective)
open import foundation.negation using (¬)
open import foundation.non-contractible-types using (is-not-contractible)
open import foundation.universe-levels using (Level; lzero; _⊔_; UU)
```

## Idea

The coproduct of two types `A` and `B` can be thought of as the disjoint union of `A` and `B`. 

## Definition

```agda
data coprod {l1 l2 : Level} (A : UU l1) (B : UU l2) : UU (l1 ⊔ l2)  where
  inl : A → coprod A B
  inr : B → coprod A B

ind-coprod :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (C : coprod A B → UU l3) →
  ((x : A) → C (inl x)) → ((y : B) → C (inr y)) →
  (t : coprod A B) → C t
ind-coprod C f g (inl x) = f x
ind-coprod C f g (inr x) = g x
```

## Properties

### The left and right inclusions are injective

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-injective-inl : is-injective {B = coprod A B} inl
  is-injective-inl refl = refl

  is-injective-inr : is-injective {B = coprod A B} inr
  is-injective-inr refl = refl 

  neq-inl-inr : {x : A} {y : B} → ¬ (Id (inl x) (inr y))
  neq-inl-inr ()

  neq-inr-inl : {x : B} {y : A} → ¬ (Id (inr x) (inl y))
  neq-inr-inl ()
```

### Coproducts of contractible types are not contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-not-contractible-coprod-is-contr :
      is-contr A → is-contr B → is-not-contractible (coprod A B)
    is-not-contractible-coprod-is-contr HA HB HAB =
      neq-inl-inr {x = center HA} {y = center HB} (eq-is-contr  HAB)
```
