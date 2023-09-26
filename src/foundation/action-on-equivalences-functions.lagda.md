# Action on equivalences of functions

```agda
module foundation.action-on-equivalences-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-induction
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

Applying the
[action on identifications](foundation.action-on-identifications-functions.md)
to [identifications](foundation-core.identity-types.md) arising from the
[univalence axiom](foundation.univalence.md) gives us the **action on
equivalences**.

Alternatively, one can apply
[transport along identifications](foundation-core.transport-along-identifications.md)
to get
[transport along equivalences](foundation.transport-along-equivalences.md), but
luckily, these two notions coincide.

## Definition

```agda
module _
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B)
  where

  abstract
    unique-action-equiv-function :
      (X : UU l1) →
      is-contr
        ( Σ ((Y : UU l1) → X ≃ Y → f X ＝ f Y) (λ h → h X id-equiv ＝ refl))
    unique-action-equiv-function X =
      is-contr-map-ev-id-equiv
        ( λ Y e → f X ＝ f Y)
        ( refl)

  action-equiv-function :
    {X Y : UU l1} → X ≃ Y → f X ＝ f Y
  action-equiv-function {X} {Y} e = ap f (eq-equiv X Y e)

  compute-action-equiv-function-id-equiv :
    (X : UU l1) → action-equiv-function id-equiv ＝ refl
  compute-action-equiv-function-id-equiv X =
    ap (ap f) (compute-eq-equiv-id-equiv X)
```

## Properties

### The action on equivalences of a constant map is constant

```agda
compute-action-equiv-function-const :
  {l1 l2 : Level} {B : UU l2} (b : B) {X Y : UU l1}
  (e : X ≃ Y) → (action-equiv-function (const (UU l1) B b) e) ＝ refl
compute-action-equiv-function-const b {X} {Y} e = ap-const b (eq-equiv X Y e)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-action-equiv-function-comp-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  action-equiv-function f (e' ∘e e) ＝
  action-equiv-function f e ∙ action-equiv-function f e'
distributive-action-equiv-function-comp-equiv f {X} {Y} {Z} e e' =
    ( ap (ap f) (inv (compute-eq-equiv-comp-equiv X Y Z e e'))) ∙
    ( ap-concat f (eq-equiv X Y e) (eq-equiv Y Z e'))
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-equiv-function-inv-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1}
  (e : X ≃ Y) →
  action-equiv-function f (inv-equiv e) ＝ inv (action-equiv-function f e)
compute-action-equiv-function-inv-equiv f {X} {Y} e =
  ( ap (ap f) (inv (commutativity-inv-eq-equiv X Y e))) ∙
  ( ap-inv f (eq-equiv X Y e))
```
