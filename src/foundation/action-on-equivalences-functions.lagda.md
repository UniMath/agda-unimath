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
[transport along identifications](foundation-core.transport.md) to get
[transport along equivalences](foundation.transport-along-equivalences.md), but
luckily, these two notions coincide.

## Definition

```agda
action-equiv-function :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1} →
  X ≃ Y → f X ＝ f Y
action-equiv-function f {X} {Y} e = ap f (eq-equiv X Y e)

action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X ≃ f Y
action-equiv-family f = equiv-eq ∘ action-equiv-function f

map-action-equiv-family :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X → f Y
map-action-equiv-family f = map-equiv ∘ action-equiv-family f
```

## Properties

### The identity function acts trivially on equivalences

```agda
compute-action-equiv-family-id :
  {l : Level} {X Y : UU l} (e : X ≃ Y) → (action-equiv-family id e) ＝ e
compute-action-equiv-family-id {l} {X} {Y} e =
  (ap equiv-eq (ap-id (eq-equiv X Y e))) ∙ (is-section-eq-equiv e)
```

### The action on equivalences of a composite function is the composite of the actions

```agda
distributive-action-equiv-function-comp :
  {l1 l2 l3 : Level} {C : UU l3} (g : UU l2 → C) (f : UU l1 → UU l2)
  {X Y : UU l1} → action-equiv-function (g ∘ f) ~ (action-equiv-function g ∘ action-equiv-family f)
distributive-action-equiv-function-comp g f {X} {Y} e =
  ( ap-comp g f (eq-equiv X Y e)) ∙
  ( ap (ap g) (inv (is-retraction-eq-equiv (action-equiv-function f e))))

distributive-action-equiv-family-comp :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2)
  {X Y : UU l1} → action-equiv-family (g ∘ f) ~ (action-equiv-family g ∘ action-equiv-family f)
distributive-action-equiv-family-comp g f {X} {Y} e =
  ap equiv-eq (distributive-action-equiv-function-comp g f {X} {Y} e)
```

### The action on equivalences of any map preserves `id-equiv`

```agda
compute-action-equiv-function-id-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) (A : UU l1) →
  (action-equiv-function f id-equiv) ＝ refl
compute-action-equiv-function-id-equiv f A = ap (ap f) (compute-eq-equiv-id-equiv A)

compute-action-equiv-family-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) (A : UU l1) →
  (action-equiv-family f id-equiv) ＝ id-equiv
compute-action-equiv-family-id-equiv f A = ap equiv-eq (compute-action-equiv-function-id-equiv f A)
```

### The action on equivalences of a constant map is constant

```agda
compute-action-equiv-function-const :
  {l1 l2 : Level} {B : UU l2} (b : B) {X Y : UU l1}
  (e : X ≃ Y) → (action-equiv-function (const (UU l1) B b) e) ＝ refl
compute-action-equiv-function-const b {X} {Y} e = ap-const b (eq-equiv X Y e)

compute-action-equiv-family-const :
  {l1 l2 : Level} (B : UU l2) {X Y : UU l1}
  (e : X ≃ Y) → (action-equiv-family (const (UU l1) (UU l2) B) e) ＝ id-equiv
compute-action-equiv-family-const B {X} {Y} e = ap equiv-eq (compute-action-equiv-function-const B e)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-action-equiv-function-comp-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  action-equiv-function f (e' ∘e e) ＝ (action-equiv-function f e ∙ action-equiv-function f e')
distributive-action-equiv-function-comp-equiv f {X} {Y} {Z} e e' =
    ( ap (ap f) (inv (compute-eq-equiv-comp-equiv X Y Z e e'))) ∙
    ( ap-concat f (eq-equiv X Y e) (eq-equiv Y Z e'))

distributive-action-equiv-family-comp-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  action-equiv-family f (e' ∘e e) ＝ (action-equiv-family f e' ∘e action-equiv-family f e)
distributive-action-equiv-family-comp-equiv f {X} {Y} {Z} e e' =
  ( ap equiv-eq (distributive-action-equiv-function-comp-equiv f e e')) ∙
  ( inv (compute-equiv-eq-concat (action-equiv-function f e) (action-equiv-function f e')))
```

### The action on equivalences of any map preserves inverses

```agda
compute-action-equiv-function-inv-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1}
  (e : X ≃ Y) → action-equiv-function f (inv-equiv e) ＝ inv (action-equiv-function f e)
compute-action-equiv-function-inv-equiv f {X} {Y} e =
  ( ap (ap f) (inv (commutativity-inv-eq-equiv X Y e))) ∙
  ( ap-inv f (eq-equiv X Y e))

compute-action-equiv-family-inv-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → action-equiv-family f (inv-equiv e) ＝ inv-equiv (action-equiv-family f e)
compute-action-equiv-family-inv-equiv f {X} {Y} e =
  ( ap equiv-eq (compute-action-equiv-function-inv-equiv f e)) ∙
  ( inv (commutativity-inv-equiv-eq (f X) (f Y) (action-equiv-function f e)))
```
