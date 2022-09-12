---
title: Decidable propositions
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.decidable-propositions where

open import foundation-core.cartesian-product-types
open import foundation-core.dependent-pair-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.universe-levels

open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.double-negation
open import foundation.negation
```

## Idea

A decidable proposition is a proposition that has a decidable underlying type.

## Definition

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = Σ (UU l) is-decidable-prop
```

###

```agda
abstract
  is-prop-is-decidable :
    {l : Level} {A : UU l} → is-prop A → is-prop (is-decidable A)
  is-prop-is-decidable is-prop-A =
    is-prop-coprod intro-dn is-prop-A is-prop-neg

is-decidable-Prop :
  {l : Level} → UU-Prop l → UU-Prop l
pr1 (is-decidable-Prop P) = is-decidable (type-Prop P)
pr2 (is-decidable-Prop P) = is-prop-is-decidable (is-prop-type-Prop P)
```

```agda
module _
  {l : Level} (P : decidable-Prop l)
  where

  prop-decidable-Prop : UU-Prop l
  prop-decidable-Prop = tot (λ x → pr1) P

  type-decidable-Prop : UU l
  type-decidable-Prop = type-Prop prop-decidable-Prop

  abstract
    is-prop-type-decidable-Prop : is-prop type-decidable-Prop
    is-prop-type-decidable-Prop = is-prop-type-Prop prop-decidable-Prop

  is-decidable-type-decidable-Prop : is-decidable type-decidable-Prop
  is-decidable-type-decidable-Prop = pr2 (pr2 P)

  is-decidable-prop-type-decidable-Prop : is-decidable-prop type-decidable-Prop
  is-decidable-prop-type-decidable-Prop = pr2 P

  is-decidable-prop-decidable-Prop : UU-Prop l
  pr1 is-decidable-prop-decidable-Prop = is-decidable type-decidable-Prop
  pr2 is-decidable-prop-decidable-Prop =
    is-prop-is-decidable is-prop-type-decidable-Prop
```
