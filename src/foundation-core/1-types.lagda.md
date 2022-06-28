# 1-Types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation-core.1-types where

open import foundation-core.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation-core.identity-types using (_＝_)
open import foundation-core.propositions using (is-prop; UU-Prop)
open import foundation-core.sets using (UU-Set)
open import foundation-core.truncated-types using
  ( is-trunc; truncated-type-succ-Truncated-Type)
open import foundation-core.truncation-levels using (one-𝕋; zero-𝕋)
open import foundation-core.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Definition

A 1-type is a type that is 1-truncated.

```agda
is-1-type : {l : Level} → UU l → UU l
is-1-type = is-trunc one-𝕋

UU-1-Type : (l : Level) → UU (lsuc l)
UU-1-Type l = Σ (UU l) is-1-type

type-1-Type : {l : Level} → UU-1-Type l → UU l
type-1-Type = pr1

abstract
  is-1-type-type-1-Type :
    {l : Level} (A : UU-1-Type l) → is-1-type (type-1-Type A)
  is-1-type-type-1-Type = pr2
```

## Properties

### The identity type of a 1-type takes values in sets

```agda
Id-Set : {l : Level} (X : UU-1-Type l) (x y : type-1-Type X) → UU-Set l
pr1 (Id-Set X x y) = (x ＝ y)
pr2 (Id-Set X x y) = is-1-type-type-1-Type X x y
```

### Any set is a 1-type

```agda
1-type-Set :
  {l : Level} → UU-Set l → UU-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A
```
