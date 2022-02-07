# 1-Types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.1-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop; UU-Prop)
open import foundation.sets using (UU-Set)
open import foundation.truncated-types using
  ( is-trunc; truncated-type-succ-Truncated-Type; is-prop-is-trunc; is-trunc-Π;
    is-trunc-function-type)
open import foundation.truncation-levels using (one-𝕋; zero-𝕋)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
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
pr1 (Id-Set X x y) = Id x y
pr2 (Id-Set X x y) = is-1-type-type-1-Type X x y
```

### Any set is a 1-type

```agda
1-type-Set :
  {l : Level} → UU-Set l → UU-1-Type l
1-type-Set A = truncated-type-succ-Truncated-Type zero-𝕋 A
```

### Being a 1-type is a property

```agda
abstract
  is-prop-is-1-type :
    {l : Level} (A : UU l) → is-prop (is-1-type A)
  is-prop-is-1-type A = is-prop-is-trunc one-𝕋 A

is-1-type-Prop :
  {l : Level} → UU l → UU-Prop l
pr1 (is-1-type-Prop A) = is-1-type A
pr2 (is-1-type-Prop A) = is-prop-is-1-type A
```

### Products of families of 1-types are 1-types

```agda
abstract
  is-1-type-Π :
    {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    ((x : A) → is-1-type (B x)) → is-1-type ((x : A) → B x)
  is-1-type-Π = is-trunc-Π one-𝕋

type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU (l1 ⊔ l2)
type-Π-1-Type' A B = (x : A) → type-1-Type (B x)

is-1-type-type-Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type' A B)
is-1-type-type-Π-1-Type' A B =
  is-1-type-Π (λ x → is-1-type-type-1-Type (B x))

Π-1-Type' :
  {l1 l2 : Level} (A : UU l1) (B : A → UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
pr1 (Π-1-Type' A B) = type-Π-1-Type' A B
pr2 (Π-1-Type' A B) = is-1-type-type-Π-1-Type' A B

type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU (l1 ⊔ l2)
type-Π-1-Type A B = type-Π-1-Type' (type-1-Type A) B

is-1-type-type-Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  is-1-type (type-Π-1-Type A B)
is-1-type-type-Π-1-Type A B =
  is-1-type-type-Π-1-Type' (type-1-Type A) B

Π-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : type-1-Type A → UU-1-Type l2) →
  UU-1-Type (l1 ⊔ l2)
pr1 (Π-1-Type A B) = type-Π-1-Type A B
pr2 (Π-1-Type A B) = is-1-type-type-Π-1-Type A B
```

### The type of functions into a 1-type is a 1-type

```agda
abstract
  is-1-type-function-type :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    is-1-type B → is-1-type (A → B)
  is-1-type-function-type = is-trunc-function-type one-𝕋

type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU (l1 ⊔ l2)
type-hom-1-Type A B = type-1-Type A → type-1-Type B

is-1-type-type-hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) →
  is-1-type (type-hom-1-Type A B)
is-1-type-type-hom-1-Type A B =
  is-1-type-function-type (is-1-type-type-1-Type B)

hom-1-Type :
  {l1 l2 : Level} (A : UU-1-Type l1) (B : UU-1-Type l2) → UU-1-Type (l1 ⊔ l2)
pr1 (hom-1-Type A B) = type-hom-1-Type A B
pr2 (hom-1-Type A B) = is-1-type-type-hom-1-Type A B
```

