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
eq-ap-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1} →
  X ≃ Y → f X ＝ f Y
eq-ap-equiv f {X} {Y} e = ap f (eq-equiv X Y e)

ap-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X ≃ f Y
ap-equiv f = equiv-eq ∘ eq-ap-equiv f

map-ap-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → f X → f Y
map-ap-equiv f = map-equiv ∘ ap-equiv f
```

## Properties

### The identity function acts trivially on equivalences

```agda
compute-ap-equiv-id :
  {l : Level} {X Y : UU l} (e : X ≃ Y) → (ap-equiv id e) ＝ e
compute-ap-equiv-id {l} {X} {Y} e =
  (ap equiv-eq (ap-id (eq-equiv X Y e))) ∙ (is-section-eq-equiv e)
```

### The action on equivalences of a composite function is the composite of the actions

```agda
distributive-eq-ap-equiv-comp :
  {l1 l2 l3 : Level} {C : UU l3} (g : UU l2 → C) (f : UU l1 → UU l2)
  {X Y : UU l1} → eq-ap-equiv (g ∘ f) ~ (eq-ap-equiv g ∘ ap-equiv f)
distributive-eq-ap-equiv-comp g f {X} {Y} e =
  ( ap-comp g f (eq-equiv X Y e)) ∙
  ( ap (ap g) (inv (is-retraction-eq-equiv (eq-ap-equiv f e))))

distributive-ap-equiv-comp :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2)
  {X Y : UU l1} → ap-equiv (g ∘ f) ~ (ap-equiv g ∘ ap-equiv f)
distributive-ap-equiv-comp g f {X} {Y} e =
  ap equiv-eq (distributive-eq-ap-equiv-comp g f {X} {Y} e)
```

### The action on equivalences of any map preserves `id-equiv`

```agda
compute-eq-ap-equiv-id-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) (A : UU l1) →
  (eq-ap-equiv f id-equiv) ＝ refl
compute-eq-ap-equiv-id-equiv f A = ap (ap f) (compute-eq-equiv-id-equiv A)

compute-ap-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) (A : UU l1) →
  (ap-equiv f id-equiv) ＝ id-equiv
compute-ap-equiv-id-equiv f A = ap equiv-eq (compute-eq-ap-equiv-id-equiv f A)
```

### The action on equivalences of a constant map is constant

```agda
compute-eq-ap-equiv-const :
  {l1 l2 : Level} {B : UU l2} (b : B) {X Y : UU l1}
  (e : X ≃ Y) → (eq-ap-equiv (const (UU l1) B b) e) ＝ refl
compute-eq-ap-equiv-const b {X} {Y} e = ap-const b (eq-equiv X Y e)

compute-ap-equiv-const :
  {l1 l2 : Level} (B : UU l2) {X Y : UU l1}
  (e : X ≃ Y) → (ap-equiv (const (UU l1) (UU l2) B) e) ＝ id-equiv
compute-ap-equiv-const B {X} {Y} e = ap equiv-eq (compute-eq-ap-equiv-const B e)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
distributive-eq-ap-equiv-comp-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  eq-ap-equiv f (e' ∘e e) ＝ (eq-ap-equiv f e ∙ eq-ap-equiv f e')
distributive-eq-ap-equiv-comp-equiv f {X} {Y} {Z} e e' =
    ( ap (ap f) (inv (compute-eq-equiv-equiv-comp X Y Z e e'))) ∙
    ( ap-concat f (eq-equiv X Y e) (eq-equiv Y Z e'))

distributive-ap-equiv-comp-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  ap-equiv f (e' ∘e e) ＝ (ap-equiv f e' ∘e ap-equiv f e)
distributive-ap-equiv-comp-equiv f {X} {Y} {Z} e e' =
  ( ap equiv-eq (distributive-eq-ap-equiv-comp-equiv f e e')) ∙
  ( inv (compute-equiv-eq-concat (eq-ap-equiv f e) (eq-ap-equiv f e')))
```

### The action on equivalences of any map preserves inverses

```agda
compute-eq-ap-equiv-inv-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1}
  (e : X ≃ Y) → eq-ap-equiv f (inv-equiv e) ＝ inv (eq-ap-equiv f e)
compute-eq-ap-equiv-inv-equiv f {X} {Y} e =
  ( ap (ap f) (inv (commutativity-inv-eq-equiv X Y e))) ∙
  ( ap-inv f (eq-equiv X Y e))

compute-ap-equiv-inv-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → ap-equiv f (inv-equiv e) ＝ inv-equiv (ap-equiv f e)
compute-ap-equiv-inv-equiv f {X} {Y} e =
  ( ap equiv-eq (compute-eq-ap-equiv-inv-equiv f e)) ∙
  ( inv (commutativity-inv-equiv-eq (f X) (f Y) (eq-ap-equiv f e)))
```
