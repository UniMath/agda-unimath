# Decidable propositions

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.decidable-propositions where

open import foundation.cartesian-product-types using (_×_)
open import foundation.decidable-types using
  ( is-decidable; is-prop-is-decidable)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.propositions using
  ( is-prop; UU-Prop; type-Prop; is-prop-type-Prop; is-prop-is-inhabited;
    is-prop-prod; is-prop-is-prop)
open import foundation.universe-levels using (Level; UU; lsuc)
```

## Idea

A decidable proposition is a proposition that is decidable.

## Definition

```agda
is-decidable-prop : {l : Level} → UU l → UU l
is-decidable-prop A = is-prop A × is-decidable A

decidable-Prop :
  (l : Level) → UU (lsuc l)
decidable-Prop l = Σ (UU l) is-decidable-prop

module _
  {l : Level} (P : decidable-Prop l)
  where

  prop-decidable-Prop : UU-Prop l
  pr1 prop-decidable-Prop = pr1 P
  pr2 prop-decidable-Prop = pr1 (pr2 P)

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

## Properties

### Being a decidable proposition is a property

```agda
abstract
  is-prop-is-decidable-prop :
    {l : Level} (X : UU l) → is-prop (is-decidable-prop X)
  is-prop-is-decidable-prop X =
    is-prop-is-inhabited
      ( λ H →
        is-prop-prod
          ( is-prop-is-prop X)
          ( is-prop-is-decidable (pr1 H)))
```
