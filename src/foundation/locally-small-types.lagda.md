# Locally small types

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.locally-small-types where

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (map-equiv; equiv-ap; _≃_)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id)
open import foundation.propositions using (is-prop; is-prop-Π; UU-Prop)
open import foundation.small-types using
  ( is-small; is-small-is-contr; is-small-equiv; is-small-Π; is-prop-is-small)
open import foundation.univalence using (equiv-univalence)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

A type is said to be locally small if its identity types are small.

## Definition

```agda
is-locally-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-locally-small l A = (x y : A) → is-small l (Id x y)
```

## Properties

### Any small type is locally small

```agda
abstract
  is-locally-small-is-small :
    (l : Level) {l1 : Level} {A : UU l1} → is-small l A → is-locally-small l A
  pr1 (is-locally-small-is-small l (pair X e) x y) =
    Id (map-equiv e x) (map-equiv e y)
  pr2 (is-locally-small-is-small l (pair X e) x y) = equiv-ap e x y
```

### Any proposition is locally small

```agda
abstract
  is-locally-small-is-prop :
    (l : Level) {l1 : Level} {A : UU l1} → is-prop A → is-locally-small l A
  is-locally-small-is-prop l H x y = is-small-is-contr l (H x y)
```

### Any univalent universe is locally small

```agda
abstract
  is-locally-small-UU :
    {l : Level} → is-locally-small l (UU l)
  pr1 (is-locally-small-UU X Y) = X ≃ Y
  pr2 (is-locally-small-UU X Y) = equiv-univalence
```

### Any product of locally small types indexed by a small type is small

```agda
abstract
  is-locally-small-Π :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-small l A → ((x : A) → is-locally-small l (B x)) →
    is-locally-small l ((x : A) → B x)
  is-locally-small-Π l H K f g =
    is-small-equiv l (f ~ g) equiv-funext
      ( is-small-Π l H (λ x → K x (f x) (g x)))
```

### Being locally small is a property

```agda
abstract
  is-prop-is-locally-small :
    (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-locally-small l A)
  is-prop-is-locally-small l A =
    is-prop-Π (λ x → is-prop-Π (λ y → is-prop-is-small l (Id x y)))

is-locally-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU-Prop (lsuc l ⊔ l1)
pr1 (is-locally-small-Prop l A) = is-locally-small l A
pr2 (is-locally-small-Prop l A) = is-prop-is-locally-small l A
```
