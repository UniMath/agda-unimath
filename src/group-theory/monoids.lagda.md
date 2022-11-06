---
title: Monoids
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.monoids where

open import foundation.cartesian-product-types using (_×_)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; inv; _∙_)
open import foundation.propositions using
  ( all-elements-equal; is-prop-all-elements-equal; is-prop; Prop;
    prod-Prop; Π-Prop)
open import foundation.sets using (Set; is-set; type-Set; Id-Prop)
open import foundation.subtypes using (eq-type-subtype)
open import foundation.unital-binary-operations using (is-unital)
open import foundation.universe-levels using (Level; UU; lsuc)

open import group-theory.semigroups using
  ( Semigroup; type-Semigroup; mul-Semigroup; set-Semigroup;
    is-set-type-Semigroup; associative-mul-Semigroup)
```

## Idea

Monoids are unital semigroups

## Definition

```agda
is-unital-Semigroup :
  {l : Level} → Semigroup l → UU l
is-unital-Semigroup G = is-unital (mul-Semigroup G)

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semigroup l) is-unital-Semigroup

semigroup-Monoid :
  {l : Level} (M : Monoid l) → Semigroup l
semigroup-Monoid M = pr1 M

type-Monoid : {l : Level} (M : Monoid l) → UU l
type-Monoid M = type-Semigroup (semigroup-Monoid M)

set-Monoid : {l : Level} (M : Monoid l) → Set l
set-Monoid M = set-Semigroup (semigroup-Monoid M)

is-set-type-Monoid :
  {l : Level} (M : Monoid l) → is-set (type-Monoid M)
is-set-type-Monoid M = is-set-type-Semigroup (semigroup-Monoid M)

mul-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid M = mul-Semigroup (semigroup-Monoid M)

mul-Monoid' :
  {l : Level} (M : Monoid l) → type-Monoid M → type-Monoid M → type-Monoid M
mul-Monoid' M y x = mul-Monoid M x y

associative-mul-Monoid :
  {l : Level} (M : Monoid l) (x y z : type-Monoid M) →
  Id (mul-Monoid M (mul-Monoid M x y) z) (mul-Monoid M x (mul-Monoid M y z))
associative-mul-Monoid M =
  associative-mul-Semigroup (semigroup-Monoid M)

unit-Monoid :
  {l : Level} (M : Monoid l) → type-Monoid M
unit-Monoid M = pr1 (pr2 M)

left-unit-law-mul-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M (unit-Monoid M) x) x
left-unit-law-mul-Monoid M = pr1 (pr2 (pr2 M))

right-unit-law-mul-Monoid :
  {l : Level} (M : Monoid l) (x : type-Monoid M) →
  Id (mul-Monoid M x (unit-Monoid M)) x
right-unit-law-mul-Monoid M = pr2 (pr2 (pr2 M))
```

## Properties

### For any semigroup `G`, being unital is a property

```agda
abstract
  all-elements-equal-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → all-elements-equal (is-unital-Semigroup G)
  all-elements-equal-is-unital-Semigroup (pair X (pair μ assoc-μ))
    (pair e (pair left-unit-e right-unit-e))
    (pair e' (pair left-unit-e' right-unit-e')) =
    eq-type-subtype
      ( λ e →
        prod-Prop
          ( Π-Prop (type-Set X) (λ y → Id-Prop X (μ e y) y))
          ( Π-Prop (type-Set X) (λ x → Id-Prop X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-unital-Semigroup G)
  is-prop-is-unital-Semigroup G =
    is-prop-all-elements-equal (all-elements-equal-is-unital-Semigroup G)

is-unital-Semigroup-Prop : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-unital-Semigroup-Prop G) = is-unital-Semigroup G
pr2 (is-unital-Semigroup-Prop G) = is-prop-is-unital-Semigroup G
```
