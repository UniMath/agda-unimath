---
title: Small types
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.small-types where

open import foundation.booleans using (bool)
open import foundation.contractible-types using
  ( is-contr; equiv-is-contr; is-contr-equiv')
open import foundation.decidable-propositions using
  ( decidable-Prop; equiv-bool-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; is-equiv-map-equiv; map-inv-equiv; _∘e_; inv-equiv;
    isretr-map-inv-equiv; equiv-inv-equiv; equiv-precomp-equiv)
open import foundation.functoriality-dependent-function-types using
  ( equiv-Π)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-Σ; equiv-tot)
open import foundation.identity-types using (equiv-tr; inv)
open import foundation.mere-equivalences using (mere-equiv)
open import foundation.propositional-truncations using
  ( apply-universal-property-trunc-Prop)
open import foundation.propositions using
  ( is-prop; is-prop-is-proof-irrelevant; UU-Prop)
open import foundation.raising-universe-levels using (raise; equiv-raise)
open import foundation.type-arithmetic-dependent-pair-types using
  ( equiv-left-swap-Σ)
open import foundation.unit-type using (raise-unit; is-contr-raise-unit)
open import foundation.univalence using (is-contr-total-equiv)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)
```

## Idea

A type is said to be small with respect to a universe `UU l` if it is equivalent to a type in `UU l`.

## Definitions

### Small types

```agda
is-small :
  (l : Level) {l1 : Level} (A : UU l1) → UU (lsuc l ⊔ l1)
is-small l A = Σ (UU l) (λ X → A ≃ X)

type-is-small :
  {l l1 : Level} {A : UU l1} → is-small l A → UU l
type-is-small = pr1

equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A ≃ type-is-small H
equiv-is-small = pr2

map-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → A → type-is-small H
map-equiv-is-small H = map-equiv (equiv-is-small H)

map-inv-equiv-is-small :
  {l l1 : Level} {A : UU l1} (H : is-small l A) → type-is-small H → A
map-inv-equiv-is-small H = map-inv-equiv (equiv-is-small H)
```

### The universe of `UU l1`-small types in a universe `UU l2`

```agda
UU-is-small : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
UU-is-small l1 l2 = Σ (UU l2) (is-small l1)
```

## Properties

### Every type of universe level `l` is `UU (lsuc l)`-small

```agda
is-small-lsuc : {l : Level} (X : UU l) → is-small (lsuc l) X
is-small-lsuc X = pair (raise _ X) (equiv-raise _ X)
```

### Small types are closed under equivalences

```agda
abstract
  is-small-equiv :
    (l : Level) {l1 l2 : Level} {A : UU l1} (B : UU l2) →
    A ≃ B → is-small l B → is-small l A
  pr1 (is-small-equiv l B e (pair X h)) = X
  pr2 (is-small-equiv l B e (pair X h)) = h ∘e e

abstract
  is-small-equiv' :
    (l : Level) {l1 l2 : Level} (A : UU l1) {B : UU l2} →
    A ≃ B → is-small l A → is-small l B
  is-small-equiv' l A e = is-small-equiv l A (inv-equiv e)

abstract
  is-small-Σ :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-small l A → ((x : A) → is-small l (B x)) → is-small l (Σ A B)
  pr1 (is-small-Σ l {B = B} (pair X e) H) =
    Σ X (λ x → pr1 (H (map-inv-equiv e x)))
  pr2 (is-small-Σ l {B = B} (pair X e) H) =
    equiv-Σ
      ( λ x → pr1 (H (map-inv-equiv e x)))
      ( e)
      ( λ a →
        ( equiv-tr
          ( λ t → pr1 (H t))
          ( inv (isretr-map-inv-equiv e a))) ∘e
        ( pr2 (H a)))
```

### Any contractible type is small

```agda
abstract
  is-small-is-contr :
    (l : Level) {l1 : Level} {A : UU l1} → is-contr A → is-small l A
  pr1 (is-small-is-contr l H) = raise-unit l
  pr2 (is-small-is-contr l H) = equiv-is-contr H is-contr-raise-unit
```

### Any product of small types indexed by a small type is small

```agda
abstract
  is-small-Π :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
    is-small l A → ((x : A) → is-small l (B x)) → is-small l ((x : A) → B x)
  pr1 (is-small-Π l {B = B} (pair X e) H) =
    (x : X) → pr1 (H (map-inv-equiv e x))
  pr2 (is-small-Π l {B = B} (pair X e) H) =
    equiv-Π
      ( λ (x : X) → pr1 (H (map-inv-equiv e x)))
      ( e)
      ( λ a →
        ( equiv-tr
          ( λ t → pr1 (H t))
          ( inv (isretr-map-inv-equiv e a))) ∘e
        ( pr2 (H a)))
```

### The universe of `UU l1`-small types in `UU l2` is equivalent to the universe of `UU l2`-small types in `UU l1`

```agda
equiv-UU-is-small :
  (l1 l2 : Level) → UU-is-small l1 l2 ≃ UU-is-small l2 l1
equiv-UU-is-small l1 l2 =
  ( equiv-tot (λ X → equiv-tot (λ Y → equiv-inv-equiv))) ∘e
  ( equiv-left-swap-Σ)
```

### The type of decidable propositions in any universe is small

```agda
abstract
  is-small-decidable-Prop :
    (l1 l2 : Level) → is-small l2 (decidable-Prop l1)
  pr1 (is-small-decidable-Prop l1 l2) = raise l2 bool
  pr2 (is-small-decidable-Prop l1 l2) =
    equiv-raise l2 bool ∘e equiv-bool-decidable-Prop
```

### Being small is a property

```agda
abstract
  is-prop-is-small :
    (l : Level) {l1 : Level} (A : UU l1) → is-prop (is-small l A)
  is-prop-is-small l A =
    is-prop-is-proof-irrelevant
      ( λ Xe →
        is-contr-equiv'
          ( Σ (UU l) (λ Y → (pr1 Xe) ≃ Y))
          ( equiv-tot ((λ Y → equiv-precomp-equiv (pr2 Xe) Y)))
          ( is-contr-total-equiv (pr1 Xe)))

is-small-Prop :
  (l : Level) {l1 : Level} (A : UU l1) → UU-Prop (lsuc l ⊔ l1)
pr1 (is-small-Prop l A) = is-small l A
pr2 (is-small-Prop l A) = is-prop-is-small l A
```

### Being small is closed under mere equivalences

```agda
abstract
  is-small-mere-equiv :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} → mere-equiv A B →
    is-small l B → is-small l A
  is-small-mere-equiv l e H =
    apply-universal-property-trunc-Prop e
      ( is-small-Prop l _)
      ( λ e' → is-small-equiv l _ e' H)
```
