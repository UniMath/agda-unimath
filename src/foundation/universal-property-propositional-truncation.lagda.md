# The universal property of propositional truncations

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-propositional-truncation where

open import foundation.contractible-maps using
  ( is-contr-map-is-equiv; is-equiv-is-contr-map)
open import foundation.contractible-types using
  ( is-contr; is-contr-equiv'; center; is-contr-equiv)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( is-equiv; map-inv-is-equiv; map-equiv; is-subtype-is-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-pair-types using (equiv-tot)
open import foundation.homotopies using (_~_)
open import foundation.identity-types using (Id)
open import foundation.propositions using
  ( UU-Prop; type-Prop; is-prop-type-Prop; type-hom-Prop; is-equiv-is-prop;
    is-prop-Π; type-equiv-Prop)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)
```

## Idea

A map `f : A → P` into a proposition `P` is said to satisfy the universal property of the propositional truncation of `A`, or is simply said to be a propositional truncation of `A`, if any map `g : A → Q` into a proposition `Q` extends uniquely along `f`.

## Definition

### The condition of being a propositional truncation

```agda
precomp-Prop :
  { l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) →
  (A → type-Prop P) → (Q : UU-Prop l3) →
  (type-hom-Prop P Q) → (A → type-Prop Q)
precomp-Prop P f Q g = g ∘ f

is-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
is-propositional-truncation l P f =
  (Q : UU-Prop l) → is-equiv (precomp-Prop P f Q)
```

### The universal property of the propositional truncation

```agda
universal-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1}
  (P : UU-Prop l2) (f : A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
universal-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) (g : A → type-Prop Q) →
  is-contr (Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~  g))
```

### Extension property of the propositional truncation

This is a simplified form of the universal properties, that works because we're mapping into propositions.

```agda
extension-property-propositional-truncation :
  ( l : Level) {l1 l2 : Level} {A : UU l1} (P : UU-Prop l2) →
  ( A → type-Prop P) → UU (lsuc l ⊔ l1 ⊔ l2)
extension-property-propositional-truncation l {A = A} P f =
  (Q : UU-Prop l) → (A → type-Prop Q) → (type-hom-Prop P Q)
```

## Properties

### Being a propositional trunction is equivalent to satisfying the universal property of the propositional truncation

```agda
abstract
  universal-property-is-propositional-truncation :
    (l : Level) {l1 l2 : Level} {A : UU l1}
    (P : UU-Prop l2) (f : A → type-Prop P) →
    is-propositional-truncation l P f →
    universal-property-propositional-truncation l P f
  universal-property-is-propositional-truncation l P f is-ptr-f Q g =
    is-contr-equiv'
      ( Σ (type-hom-Prop P Q) (λ h → Id (h ∘ f) g))
      ( equiv-tot (λ h → equiv-funext))
      ( is-contr-map-is-equiv (is-ptr-f Q) g)

abstract
  map-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    ({l : Level} → is-propositional-truncation l P f) →
    (Q : UU-Prop l3) (g : A → type-Prop Q) → type-hom-Prop P Q
  map-is-propositional-truncation P f is-ptr-f Q g =
    pr1
      ( center
        ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

  htpy-is-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (f : A → type-Prop P) →
    (is-ptr-f : {l : Level} → is-propositional-truncation l P f) →
    (Q : UU-Prop l3) (g : A → type-Prop Q) →
    ((map-is-propositional-truncation P f is-ptr-f Q g) ∘ f) ~ g
  htpy-is-propositional-truncation P f is-ptr-f Q g =
    pr2
      ( center
        ( universal-property-is-propositional-truncation _ P f is-ptr-f Q g))

abstract
  is-propositional-truncation-universal-property :
    (l : Level) {l1 l2 : Level} {A : UU l1}
    (P : UU-Prop l2) (f : A → type-Prop P) →
    universal-property-propositional-truncation l P f →
    is-propositional-truncation l P f
  is-propositional-truncation-universal-property l P f up-f Q =
    is-equiv-is-contr-map
      ( λ g → is-contr-equiv
        ( Σ (type-hom-Prop P Q) (λ h → (h ∘ f) ~ g))
        ( equiv-tot (λ h → equiv-funext))
        ( up-f Q g))
```

### Being a propositional truncation is equivalent to satisfying the extension property of propositional truncations

```agda
abstract
  is-propositional-truncation-extension-property :
    { l1 l2 : Level} {A : UU l1} (P : UU-Prop l2)
    ( f : A → type-Prop P) →
    ( {l : Level} → extension-property-propositional-truncation l P f) →
    ( {l : Level} → is-propositional-truncation l P f)
  is-propositional-truncation-extension-property P f up-P {l} Q =
    is-equiv-is-prop
      ( is-prop-Π (λ x → is-prop-type-Prop Q))
      ( is-prop-Π (λ x → is-prop-type-Prop Q))
      ( up-P Q)
```

### Uniqueness of propositional truncations

```agda
abstract
  is-equiv-is-ptruncation-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P')
    (h : type-hom-Prop P P') (H : (h ∘ f) ~ f') →
    ({l : Level} → is-propositional-truncation l P f) →
    ({l : Level} → is-propositional-truncation l P' f') →
    is-equiv h
  is-equiv-is-ptruncation-is-ptruncation P P' f f' h H is-ptr-P is-ptr-P' =
    is-equiv-is-prop
      ( is-prop-type-Prop P)
      ( is-prop-type-Prop P')
      ( map-inv-is-equiv (is-ptr-P' P) f)

abstract
  is-ptruncation-is-ptruncation-is-equiv :
    {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
    is-equiv h → ({l : Level} → is-propositional-truncation l P f) →
    ({l : Level} → is-propositional-truncation l P' f')
  is-ptruncation-is-ptruncation-is-equiv P P' f f' h is-equiv-h is-ptr-f =
    is-propositional-truncation-extension-property P' f'
      ( λ R g →
        ( map-is-propositional-truncation P f is-ptr-f R g) ∘
        ( map-inv-is-equiv is-equiv-h))

abstract
  is-ptruncation-is-equiv-is-ptruncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') (h : type-hom-Prop P P') →
    ({l : Level} → is-propositional-truncation l P' f') → is-equiv h →
    ({l : Level} → is-propositional-truncation l P f)
  is-ptruncation-is-equiv-is-ptruncation P P' f f' h is-ptr-f' is-equiv-h =
    is-propositional-truncation-extension-property P f
      ( λ R g → (map-is-propositional-truncation P' f' is-ptr-f' R g) ∘ h)

abstract
  is-uniquely-unique-propositional-truncation :
    {l1 l2 l3 : Level} {A : UU l1} (P : UU-Prop l2) (P' : UU-Prop l3)
    (f : A → type-Prop P) (f' : A → type-Prop P') →
    ({l : Level} → is-propositional-truncation l P f) →
    ({l : Level} → is-propositional-truncation l P' f') →
    is-contr (Σ (type-equiv-Prop P P') (λ e → (map-equiv e ∘ f) ~ f'))
  is-uniquely-unique-propositional-truncation P P' f f' is-ptr-f is-ptr-f' =
    is-contr-total-Eq-subtype
      ( universal-property-is-propositional-truncation _ P f is-ptr-f P' f')
      ( is-subtype-is-equiv)
      ( map-is-propositional-truncation P f is-ptr-f P' f')
      ( htpy-is-propositional-truncation P f is-ptr-f P' f')
      ( is-equiv-is-ptruncation-is-ptruncation  P P' f f'
        ( map-is-propositional-truncation P f is-ptr-f P' f')
        ( htpy-is-propositional-truncation P f is-ptr-f P' f')
        ( λ {l} → is-ptr-f)
        ( λ {l} → is-ptr-f'))
```
