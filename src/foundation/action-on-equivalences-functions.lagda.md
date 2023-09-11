# Action on equivalences of functions

```agda
module foundation.action-on-equivalences-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.homotopies
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
action-equiv-function :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1} →
  X ≃ Y → f X ＝ f Y
action-equiv-function f {X} {Y} e = ap f (eq-equiv X Y e)
```

## Properties

### The action on equivalences of any map preserves `id-equiv`

```agda
compute-action-equiv-function-id-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) (A : UU l1) →
  (action-equiv-function f id-equiv) ＝ refl
compute-action-equiv-function-id-equiv f A =
  ap (ap f) (compute-eq-equiv-id-equiv A)
```

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
