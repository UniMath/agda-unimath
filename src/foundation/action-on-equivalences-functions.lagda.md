# Action on equivalences of functions

```agda
module foundation.action-on-equivalences-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.univalence
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation.transport
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Definition

```agda
ap-eq-equiv :
  {l1 l2 : Level} {A : UU l2} (B : UU l1 → A) {X Y : UU l1} →
  X ≃ Y → B X ＝ B Y
ap-eq-equiv B {X} {Y} e = ap B (eq-equiv X Y e)

ap-equiv :
  {l1 l2 : Level} (B : UU l1 → UU l2) {X Y : UU l1} →
  X ≃ Y → B X ≃ B Y
ap-equiv B = equiv-eq ∘ ap-eq-equiv B
```

## Properties

### The identity function acts trivially on equivalences

```agda
ap-equiv-id :
  {l : Level} {X Y : UU l} (e : X ≃ Y) → (ap-equiv id e) ＝ e
ap-equiv-id {l} {X} {Y} e =
  (ap equiv-eq (ap-id (eq-equiv X Y e))) ∙ (is-section-eq-equiv e)
```

### The action on equivalences of a composite function is the composite of the actions

```agda
ap-eq-equiv-comp :
  {l1 l2 l3 : Level} {A : UU l3} (g : UU l2 → A) (f : UU l1 → UU l2)
  {X Y : UU l1} → ap-eq-equiv (g ∘ f) ~ (ap-eq-equiv g ∘ ap-equiv f)
ap-eq-equiv-comp g f {X} {Y} e =
  ( ap-comp g f (eq-equiv X Y e)) ∙
  ( ap (ap g) (inv (is-retraction-eq-equiv (ap-eq-equiv f e))))

ap-equiv-comp :
  {l1 l2 l3 : Level} (g : UU l2 → UU l3) (f : UU l1 → UU l2)
  {X Y : UU l1} → ap-equiv (g ∘ f) ~ (ap-equiv g ∘ ap-equiv f)
ap-equiv-comp g f {X} {Y} e =
  ap equiv-eq (ap-eq-equiv-comp g f {X} {Y} e)
```

### The action on equivalences of any map preserves `id-equiv`

```agda
ap-eq-equiv-id-equiv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) (A : UU l1) →
  (ap-eq-equiv f (id-equiv {A = A})) ＝ refl
ap-eq-equiv-id-equiv f A = ap (ap f) (compute-eq-equiv-id-equiv A)

ap-equiv-id-equiv :
  {l1 l2 : Level} (f : UU l1 → UU l2) (A : UU l1) →
  (ap-equiv f (id-equiv {A = A})) ＝ id-equiv {A = f A}
ap-equiv-id-equiv f A = ap equiv-eq (ap-eq-equiv-id-equiv f A)
```

### The action on equivalences of any map preserves composition of equivalences

```agda
ap-eq-equiv-equiv-comp :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  ap-eq-equiv f (e' ∘e e) ＝ (ap-eq-equiv f e ∙ ap-eq-equiv f e')
ap-eq-equiv-equiv-comp f {X} {Y} {Z} e e' =
    ( ap (ap f) (inv (compute-eq-equiv-equiv-comp X Y Z e e'))) ∙
    ( ap-concat f (eq-equiv X Y e) (eq-equiv Y Z e'))

ap-equiv-equiv-comp :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y Z : UU l1} →
  (e : X ≃ Y) (e' : Y ≃ Z) →
  ap-equiv f (e' ∘e e) ＝ (ap-equiv f e' ∘e ap-equiv f e)
ap-equiv-equiv-comp f {X} {Y} {Z} e e' =
  ( ap equiv-eq (ap-eq-equiv-equiv-comp f e e')) ∙
  ( inv (compute-equiv-eq-concat (ap-eq-equiv f e) (ap-eq-equiv f e')))
```

### The action on equivalences of any map preserves inverses

```agda
ap-eq-equiv-inv :
  {l1 l2 : Level} {B : UU l2} (f : UU l1 → B) {X Y : UU l1}
  (e : X ≃ Y) → ap-eq-equiv f (inv-equiv e) ＝ inv (ap-eq-equiv f e)
ap-eq-equiv-inv f {X} {Y} e =
  ( ap (ap f) (inv (commutativity-inv-eq-equiv X Y e))) ∙
  ( ap-inv f (eq-equiv X Y e))

ap-equiv-inv :
  {l1 l2 : Level} (f : UU l1 → UU l2) {X Y : UU l1}
  (e : X ≃ Y) → ap-equiv f (inv-equiv e) ＝ inv-equiv (ap-equiv f e)
ap-equiv-inv f {X} {Y} e =
  ( ap equiv-eq (ap-eq-equiv-inv f e)) ∙
  ( inv (commutativity-inv-equiv-eq (f X) (f Y) (ap-eq-equiv f e)))
```

### The action on equivalences of a constant map is constant

```agda
ap-eq-equiv-const :
  {l1 l2 : Level} {B : UU l2} (b : B) {X Y : UU l1}
  (e : X ≃ Y) → (ap-eq-equiv (const (UU l1) B b) e) ＝ refl
ap-eq-equiv-const b {X} {Y} e = ap-const b (eq-equiv X Y e)

ap-equiv-const :
  {l1 l2 : Level} (B : UU l2) {X Y : UU l1}
  (e : X ≃ Y) → (ap-equiv (const (UU l1) (UU l2) B) e) ＝ id-equiv
ap-equiv-const B {X} {Y} e = ap equiv-eq (ap-eq-equiv-const B e)
```
