# Coproduct types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.coproduct-types where

open import foundation.contractible-types using
  ( is-contr; eq-is-contr; center)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.empty-types using (ex-falso)
open import foundation.identity-types using (Id; refl; ap)
open import foundation.injective-maps using (is-injective)
open import foundation.negation using (¬)
open import foundation.non-contractible-types using (is-not-contractible)
open import foundation.propositions using
  ( all-elements-equal; is-prop; is-prop-all-elements-equal; eq-is-prop';
    UU-Prop; type-Prop; is-prop-type-Prop)
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

### Coproducts of mutually exclusive propositions are propositions

```agda
module _
  {l1 l2 : Level} {P : UU l1} {Q : UU l2}
  where

  abstract
    all-elements-equal-coprod :
      (P → ¬ Q) → all-elements-equal P → all-elements-equal Q →
      all-elements-equal (coprod P Q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inl p') =
      ap inl (is-prop-P p p')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inl p) (inr q') =
      ex-falso (f p q')
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inl p') =
      ex-falso (f p' q)
    all-elements-equal-coprod f is-prop-P is-prop-Q (inr q) (inr q') =
      ap inr (is-prop-Q q q')
  
  abstract
    is-prop-coprod : (P → ¬ Q) → is-prop P → is-prop Q → is-prop (coprod P Q)
    is-prop-coprod f is-prop-P is-prop-Q =
      is-prop-all-elements-equal
        ( all-elements-equal-coprod f
          ( eq-is-prop' is-prop-P)
          ( eq-is-prop' is-prop-Q))

coprod-Prop :
  {l1 l2 : Level} (P : UU-Prop l1) (Q : UU-Prop l2) →
  (type-Prop P → ¬ (type-Prop Q)) → UU-Prop (l1 ⊔ l2)
pr1 (coprod-Prop P Q H) = coprod (type-Prop P) (type-Prop Q)
pr2 (coprod-Prop P Q H) =
  is-prop-coprod H (is-prop-type-Prop P) (is-prop-type-Prop Q)
```
