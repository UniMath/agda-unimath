# Retractions

```agda
module foundation-core.retractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A **retraction** of a map `f : A → B` consists of a map `r : B → A` equipped
with a [homotopy](foundation-core.homotopies.md) `r ∘ f ~ id`. In other words, a
retraction of a map `f` is a left inverse of `f`.

## Definitions

### The type of retractions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-retraction : (f : A → B) (g : B → A) → UU l1
  is-retraction f g = g ∘ f ~ id

  retraction : (f : A → B) → UU (l1 ⊔ l2)
  retraction f = Σ (B → A) (is-retraction f)

  map-retraction : (f : A → B) → retraction f → B → A
  map-retraction f = pr1

  is-retraction-map-retraction :
    (f : A → B) (r : retraction f) → map-retraction f r ∘ f ~ id
  is-retraction-map-retraction f = pr2
```

## Properties

### For any map `i : A → B`, a retraction of `i` induces a retraction of the action on identifications of `i`

**Proof:** Suppose that `H : r ∘ i ~ id` and `p : i x ＝ i y` is an
identification in `B`. Then we get the identification

```text
     (H x)⁻¹           ap r p           H y
  x ========= r (i x) ======== r (i y) ===== y
```

This defines a map `s : (i x ＝ i y) → x ＝ y`. To see that `s ∘ ap i ~ id`,
i.e., that the concatenation

```text
     (H x)⁻¹           ap r (ap i p)           H y
  x ========= r (i x) =============== r (i y) ===== y
```

is identical to `p : x ＝ y` for all `p : x ＝ y`, we proceed by identification
elimination. Then it suffices to show that `(H x)⁻¹ ∙ (H x)` is identical to
`refl`, which is indeed the case by the left inverse law of concatenation of
identifications.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B)
  (r : B → A) (H : r ∘ i ~ id)
  where

  is-injective-has-retraction :
    {x y : A} → i x ＝ i y → x ＝ y
  is-injective-has-retraction {x} {y} p = inv (H x) ∙ (ap r p ∙ H y)

  is-retraction-is-injective-has-retraction :
    {x y : A} → is-injective-has-retraction ∘ ap i {x} {y} ~ id
  is-retraction-is-injective-has-retraction {x} refl = left-inv (H x)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (i : A → B) (R : retraction i)
  where

  is-injective-retraction :
    {x y : A} → i x ＝ i y → x ＝ y
  is-injective-retraction =
    is-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  is-retraction-is-injective-retraction :
    {x y : A} → is-injective-retraction ∘ ap i {x} {y} ~ id
  is-retraction-is-injective-retraction =
    is-retraction-is-injective-has-retraction i
      ( map-retraction i R)
      ( is-retraction-map-retraction i R)

  retraction-ap : {x y : A} → retraction (ap i {x} {y})
  pr1 retraction-ap = is-injective-retraction
  pr2 retraction-ap = is-retraction-is-injective-retraction
```

### Retractions of homotopic maps

Given a homotopy `H : f ~ g`, then if `g` has a retraction so does `f`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  {f g : A → B}
  where

  retraction-htpy-map : f ~ g → retraction g → retraction f
  retraction-htpy-map H G =
    ( map-retraction g G ,
      map-retraction g G ·l H ∙h is-retraction-map-retraction g G)
```

### Composites of retractions are retractions

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (r : retraction g) (s : retraction h)
  where

  map-retraction-comp : X → A
  map-retraction-comp = map-retraction h s ∘ map-retraction g r

  is-retraction-map-retraction-comp : is-retraction (g ∘ h) map-retraction-comp
  is-retraction-map-retraction-comp =
    ( map-retraction h s ·l (is-retraction-map-retraction g r ·r h)) ∙h
    ( is-retraction-map-retraction h s)

  retraction-comp : retraction (g ∘ h)
  pr1 retraction-comp = map-retraction-comp
  pr2 retraction-comp = is-retraction-map-retraction-comp
```

### If `g ∘ f` has a retraction then `f` has a retraction

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (r : retraction (g ∘ h))
  where

  map-retraction-right-factor : B → A
  map-retraction-right-factor = map-retraction (g ∘ h) r ∘ g

  is-retraction-map-retraction-right-factor :
    is-retraction h map-retraction-right-factor
  is-retraction-map-retraction-right-factor =
    is-retraction-map-retraction (g ∘ h) r

  retraction-right-factor : retraction h
  pr1 retraction-right-factor = map-retraction-right-factor
  pr2 retraction-right-factor = is-retraction-map-retraction-right-factor
```

### In a commuting triangle `f ~ g ∘ h`, any retraction of the left map `f` induces a retraction of the top map `h`

In a commuting triangle of the form

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      ∨ ∨
       X,
```

if `r : X → A` is a retraction of the map `f` on the left, then `r ∘ g` is a
retraction of the top map `h`.

Note: In this file we are unable to use the definition of
[commuting triangles](foundation-core.commuting-triangles-of-maps.md), because
that would result in a cyclic module dependency.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : g ∘ h ~ f)
  (r : retraction f)
  where

  map-retraction-top-map-triangle' : B → A
  map-retraction-top-map-triangle' = map-retraction f r ∘ g

  is-retraction-map-retraction-top-map-triangle' :
    is-retraction h map-retraction-top-map-triangle'
  is-retraction-map-retraction-top-map-triangle' =
    (map-retraction f r ·l H) ∙h is-retraction-map-retraction f r

  retraction-top-map-triangle' : retraction h
  pr1 retraction-top-map-triangle' =
    map-retraction-top-map-triangle'
  pr2 retraction-top-map-triangle' =
    is-retraction-map-retraction-top-map-triangle'

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  (r : retraction f)
  where

  retraction-top-map-triangle : retraction h
  retraction-top-map-triangle =
    retraction-top-map-triangle' f g h (inv-htpy H) r
```

### In a commuting triangle `f ~ g ∘ h`, retractions of `g` and `h` compose to a retraction of `f`

In a commuting triangle of the form

```text
       h
  A ------> B
   \       /
   f\     /g
     \   /
      ∨ ∨
       X,
```

if `r : X → A` is a retraction of the map `g` on the right and `s : B → A` is a
retraction of the map `h` on top, then `s ∘ r` is a retraction of the map `f` on
the left.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h)
  (r : retraction g) (s : retraction h)
  where

  map-retraction-left-map-triangle : X → A
  map-retraction-left-map-triangle = map-retraction-comp g h r s

  is-retraction-map-retraction-left-map-triangle :
    is-retraction f map-retraction-left-map-triangle
  is-retraction-map-retraction-left-map-triangle =
    ( map-retraction-comp g h r s ·l H) ∙h
    ( is-retraction-map-retraction-comp g h r s)

  retraction-left-map-triangle : retraction f
  pr1 retraction-left-map-triangle =
    map-retraction-left-map-triangle
  pr2 retraction-left-map-triangle =
    is-retraction-map-retraction-left-map-triangle
```

## See also

- Retracts of types are defined in
  [`foundation-core.retracts-of-types`](foundation-core.retracts-of-types.md).
- Retracts of arrows are defined in
  [`foundation.retracts-of-arrows`](foundation.retracts-of-arrows.md).
