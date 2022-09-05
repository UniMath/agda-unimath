---
title: Locally small types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.locally-small-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (map-equiv; equiv-ap; _≃_)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (_＝_)
open import foundation.propositions using (is-prop; is-prop-Π; UU-Prop)
open import foundation-core.small-types using
  ( is-small; is-small-is-contr; is-small-equiv; is-small-Π; is-prop-is-small;
    Small-Type; type-Small-Type; is-small-type-Small-Type)
open import foundation.univalence using (equiv-univalence)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

A type is said to be locally small if its identity types are small.

## Definition

```agda
is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (x ＝ y)
```

### The type of locally small types

```agda
Locally-Small-Type : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
Locally-Small-Type l1 l2 = Σ (UU l2) (is-locally-small l1)

module _
  {l1 l2 : Level} (A : Locally-Small-Type l1 l2)
  where

  type-Locally-Small-Type : UU l2
  type-Locally-Small-Type = pr1 A

  is-locally-small-type-Locally-Small-Type :
    is-locally-small l1 type-Locally-Small-Type
  is-locally-small-type-Locally-Small-Type = pr2 A
```

## Properties

### Being locally small is a property

```agda
is-prop-is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
is-prop-is-locally-small l A =
  is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (x ＝ y)))

is-locally-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU-Prop (lsuc l ⊔ l1)
pr1 (is-locally-small-Prop l A) = is-locally-small l A
pr2 (is-locally-small-Prop l A) = is-prop-is-locally-small l A
```

### Any small type is locally small

```agda
is-locally-small-is-small :
  (l : Level) {l1 : Level} {A : UU l1} → is-small l A → is-locally-small l A
pr1 (is-locally-small-is-small l (pair X e) x y) =
  map-equiv e x ＝ map-equiv e y
pr2 (is-locally-small-is-small l (pair X e) x y) = equiv-ap e x y
```

### Any proposition is locally small

```agda
is-locally-small-is-prop :
  (l : Level) {l1 : Level} {A : UU l1} → is-prop A → is-locally-small l A
is-locally-small-is-prop l H x y = is-small-is-contr l (H x y)
```

### Any univalent universe is locally small

```agda
is-locally-small-UU :
  {l : Level} → is-locally-small l (UU l)
pr1 (is-locally-small-UU X Y) = X ≃ Y
pr2 (is-locally-small-UU X Y) = equiv-univalence
```

### Any product of locally small types indexed by a small type is small

```agda
is-locally-small-Π :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2} →
  is-small l3 A → ((x : A) → is-locally-small l4 (B x)) →
  is-locally-small (l3 ⊔ l4) ((x : A) → B x)
is-locally-small-Π {l1} {l2} {l3} {l4} H K f g =
  is-small-equiv
    ( f ~ g)
    ( equiv-funext)
    ( is-small-Π H (λ x → K x (f x) (g x)))

Π-Locally-Small-Type :
  {l1 l2 l3 l4 : Level} (A : Small-Type l1 l2) →
  (type-Small-Type A → Locally-Small-Type l3 l4) →
  Locally-Small-Type (l1 ⊔ l3) (l2 ⊔ l4)
pr1 (Π-Locally-Small-Type A B) =
  (a : type-Small-Type A) → type-Locally-Small-Type (B a)
pr2 (Π-Locally-Small-Type A B) =
  is-locally-small-Π
    ( is-small-type-Small-Type A)
    ( λ a → is-locally-small-type-Locally-Small-Type (B a))
```
