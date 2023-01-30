---
title: The universal property of pullbacks
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.universal-property-pullbacks where

open import foundation-core.universal-property-pullbacks public

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2; triple)
open import foundation.equivalences using
  ( is-equiv; is-property-is-equiv; map-inv-is-equiv; issec-map-inv-is-equiv;
    _≃_; is-equiv-right-factor; is-equiv-left-factor; map-equiv;
    id-equiv; _∘e_; map-inv-equiv; is-equiv-map-equiv)
open import foundation.function-extensionality using (equiv-funext)
open import foundation.functions using (_∘_)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id')
open import foundation.homotopies using
  ( _·r_; _~_; _∙h_; htpy-left-whisk; refl-htpy;
    is-contr-total-htpy; equiv-concat-htpy)
open import foundation.identity-types using (_＝_; inv; ap; refl)
open import foundation.propositions using (is-prop; is-prop-Π)
open import foundation.structure-identity-principle using
  ( extensionality-Σ)
open import foundation.subtype-identity-principle using
  ( is-contr-total-Eq-subtype)
open import foundation.universe-levels using (Level; UU; _⊔_; lsuc)

open import foundation-core.commuting-squares using (coherence-square)
open import foundation-core.cones-pullbacks using
  ( cone; cone-map; htpy-cone; htpy-eq-cone; extensionality-cone)
open import foundation-core.contractible-maps using (is-contr-map-is-equiv)
open import foundation-core.functoriality-dependent-pair-types using (equiv-tot)
open import foundation-core.functoriality-function-types using
  ( is-equiv-is-equiv-postcomp; is-equiv-postcomp-is-equiv)
```

## Idea

The universal property of pullbacks describes the optimal way to complete a diagram of the form

```md
           B
           |
           |
           V

A -----> X
```

to a square

```md
C -----> B
| |
| |
V V
A -----> X
```

## Definitions

## Properties

### The universal property is a property

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} (c : cone f g C)
  where

  abstract
    is-prop-universal-property-pullback :
      is-prop (universal-property-pullback l5 f g c)
    is-prop-universal-property-pullback =
      is-prop-Π (λ C' → is-property-is-equiv (cone-map f g c))

  map-universal-property-pullback :
    ({l : Level} → universal-property-pullback l f g c) →
    {C' : UU l5} (c' : cone f g C') → C' → C
  map-universal-property-pullback up-c {C'} c' =
    map-inv-is-equiv (up-c C') c'

  eq-map-universal-property-pullback :
    (up-c : {l : Level} → universal-property-pullback l f g c) →
    {C' : UU l5} (c' : cone f g C') →
    cone-map f g c (map-universal-property-pullback up-c c') ＝ c'
  eq-map-universal-property-pullback up-c {C'} c' =
    issec-map-inv-is-equiv (up-c C') c'
```

### The homotopy of cones obtained from the universal property of pullbacks

```
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4}
  where

  htpy-cone-map-universal-property-pullback :
    (c : cone f g C) (up : {l : Level} → universal-property-pullback l f g c) →
    {l5 : Level} {C' : UU l5} (c' : cone f g C') →
    htpy-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
  htpy-cone-map-universal-property-pullback c up c' =
    htpy-eq-cone f g
      ( cone-map f g c (map-universal-property-pullback f g c up c'))
      ( c')
      ( eq-map-universal-property-pullback f g c up c')
```

### Uniquely uniqueness of pullbacks

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) {C : UU l4} {C' : UU l5}
  where

  abstract
    uniquely-unique-pullback :
      ( c' : cone f g C') (c : cone f g C) →
      ( up-c' : {l : Level} → universal-property-pullback l f g c') →
      ( up-c : {l : Level} → universal-property-pullback l f g c) →
      is-contr
        ( Σ (C' ≃ C) (λ e → htpy-cone f g (cone-map f g c (map-equiv e)) c'))
    uniquely-unique-pullback c' c up-c' up-c =
      is-contr-total-Eq-subtype
        ( uniqueness-universal-property-pullback f g c up-c C' c')
        ( is-property-is-equiv)
        ( map-universal-property-pullback f g c up-c c')
        ( htpy-cone-map-universal-property-pullback f g c up-c c')
        ( is-equiv-up-pullback-up-pullback c c'
          ( map-universal-property-pullback f g c up-c c')
          ( htpy-cone-map-universal-property-pullback f g c up-c c')
          up-c up-c')
```
