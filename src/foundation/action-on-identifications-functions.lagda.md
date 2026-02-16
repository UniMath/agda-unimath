# The action on identifications of functions

```agda
module foundation.action-on-identifications-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.constant-maps
open import foundation-core.function-types
open import foundation-core.identity-types
```

</details>

## Idea

Any function `f : A → B` preserves
[identifications](foundation-core.identity-types.md), in the sense that it maps
identifications `p : x ＝ y` in `A` to an identification `ap f p : f x ＝ f y`
in `B`. This action on identifications can be thought of as the functoriality of
identity types.

## Definition

### The functorial action of functions on identity types

```agda
ap :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A} →
  x ＝ y → f x ＝ f y
ap f refl = refl
```

## Properties

### The identity function acts trivially on identifications

```agda
module _
  {l : Level} {A : UU l} {x y : A}
  where

  ap-id : (p : x ＝ y) → ap id p ＝ p
  ap-id refl = refl

  inv-ap-id : (p : x ＝ y) → p ＝ ap id p
  inv-ap-id p = inv (ap-id p)
```

### The action on identifications of a composite function is the composite of the actions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (g : B → C) (f : A → B)
  where

  ap-comp : {x y : A} (p : x ＝ y) → ap (g ∘ f) p ＝ (ap g ∘ ap f) p
  ap-comp refl = refl

  inv-ap-comp : {x y : A} (p : x ＝ y) → (ap g ∘ ap f) p ＝ ap (g ∘ f) p
  inv-ap-comp q = inv (ap-comp q)

ap-comp-assoc :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (h : C → D) (g : B → C) (f : A → B) {x y : A} (p : x ＝ y) →
  ap (h ∘ g) (ap f p) ＝ ap h (ap (g ∘ f) p)
ap-comp-assoc h g f refl = refl
```

### The action on identifications of any map preserves `refl`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : A)
  where

  ap-refl : ap f (refl {x = x}) ＝ refl
  ap-refl = refl
```

### The action on identifications of any map preserves concatenation of identifications

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  ap-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → ap f (p ∙ q) ＝ ap f p ∙ ap f q
  ap-concat refl q = refl

  inv-ap-concat :
    {x y z : A} (p : x ＝ y) (q : y ＝ z) → ap f p ∙ ap f q ＝ ap f (p ∙ q)
  inv-ap-concat p q = inv (ap-concat p q)

  compute-right-refl-ap-concat :
    {x y : A} (p : x ＝ y) →
    ap-concat p refl ＝ ap (ap f) right-unit ∙ inv right-unit
  compute-right-refl-ap-concat refl = refl
```

### The action on identifications of any map preserves inverses

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) {x y : A}
  where

  ap-inv : (p : x ＝ y) → ap f (inv p) ＝ inv (ap f p)
  ap-inv refl = refl

  inv-ap-inv : (p : x ＝ y) → inv (ap f p) ＝ ap f (inv p)
  inv-ap-inv p = inv (ap-inv p)
```

### The action on identifications of a constant map is constant

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) {x y : A}
  where

  ap-const : (p : x ＝ y) → ap (const A b) p ＝ refl
  ap-const refl = refl

  inv-ap-const : (p : x ＝ y) → refl ＝ ap (const A b) p
  inv-ap-const p = inv (ap-const p)
```

## See also

- [Action of functions on higher identifications](foundation.action-on-higher-identifications-functions.md).
- [Action of binary functions on identifications](foundation.action-on-identifications-binary-functions.md).
- [Action of dependent functions on identifications](foundation.action-on-identifications-dependent-functions.md).
