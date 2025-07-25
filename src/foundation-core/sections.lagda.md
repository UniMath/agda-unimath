# Sections

```agda
module foundation-core.sections where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

A **section** of a map `f : A → B` consists of a map `s : B → A` equipped with a
homotopy `f ∘ s ~ id`. In other words, a section of a map `f` is a right inverse
of `f`. For example, every dependent function induces a section of the
projection map.

Note that unlike retractions, sections don't induce sections on identity types.
A map `f` equipped with a section such that all
[actions on identifications](foundation.action-on-identifications-functions.md)
`ap f : (x ＝ y) → (f x ＝ f y)` come equipped with sections is called a
[path split](foundation-core.path-split-maps.md) map. The condition of being
path split is equivalent to being an
[equivalence](foundation-core.equivalences.md).

## Definition

### The predicate of being a section of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-section : (B → A) → UU l2
  is-section g = f ∘ g ~ id
```

### The type of sections of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  section : UU (l1 ⊔ l2)
  section = Σ (B → A) (is-section f)

  map-section : section → B → A
  map-section = pr1

  is-section-map-section : (s : section) → is-section f (map-section s)
  is-section-map-section = pr2
```

## Properties

### If `g ∘ h` has a section then `g` has a section

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (s : section (g ∘ h))
  where

  map-section-left-factor : X → B
  map-section-left-factor = h ∘ map-section (g ∘ h) s

  is-section-map-section-left-factor : is-section g map-section-left-factor
  is-section-map-section-left-factor = pr2 s

  section-left-factor : section g
  pr1 section-left-factor = map-section-left-factor
  pr2 section-left-factor = is-section-map-section-left-factor
```

### Composites of sections are sections of composites

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (g : B → X) (h : A → B) (t : section h) (s : section g)
  where

  map-section-comp : X → A
  map-section-comp = map-section h t ∘ map-section g s

  is-section-map-section-comp :
    is-section (g ∘ h) map-section-comp
  is-section-map-section-comp =
    ( g ·l (is-section-map-section h t ·r map-section g s)) ∙h
    ( is-section-map-section g s)

  section-comp : section (g ∘ h)
  pr1 section-comp = map-section-comp
  pr2 section-comp = is-section-map-section-comp
```

### In a commuting triangle `g ∘ h ~ f`, any section of `f` induces a section of `g`

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

if `s : X → A` is a section of the map `f` on the left, then `h ∘ s` is a
section of the map `g` on the right.

Note: In this file we are unable to use the definition of
[commuting triangles](foundation-core.commuting-triangles-of-maps.md), because
that would result in a cyclic module dependency.

We state two versions: one with a homotopy `g ∘ h ~ f`, and the other with a
homotopy `f ~ g ∘ h`. Our convention for commuting triangles of maps is that the
homotopy is specified in the second way, i.e., as `f ~ g ∘ h`.

#### First version, with the commutativity of the triangle opposite to our convention

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H' : g ∘ h ~ f) (s : section f)
  where

  map-section-right-map-triangle' : X → B
  map-section-right-map-triangle' = h ∘ map-section f s

  is-section-map-section-right-map-triangle' :
    is-section g map-section-right-map-triangle'
  is-section-map-section-right-map-triangle' =
    (H' ·r map-section f s) ∙h is-section-map-section f s

  section-right-map-triangle' : section g
  pr1 section-right-map-triangle' =
    map-section-right-map-triangle'
  pr2 section-right-map-triangle' =
    is-section-map-section-right-map-triangle'
```

#### Second version, with the commutativity of the triangle according to our convention

We state the same result as the previous result, only with the homotopy
witnessing the commutativity of the triangle inverted.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) (s : section f)
  where

  map-section-right-map-triangle : X → B
  map-section-right-map-triangle =
    map-section-right-map-triangle' f g h (inv-htpy H) s

  is-section-map-section-right-map-triangle :
    is-section g map-section-right-map-triangle
  is-section-map-section-right-map-triangle =
    is-section-map-section-right-map-triangle' f g h (inv-htpy H) s

  section-right-map-triangle : section g
  section-right-map-triangle =
    section-right-map-triangle' f g h (inv-htpy H) s
```

### Composites of sections in commuting triangles are sections

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

if `s : X → B` is a section of the map `g` on the right and `t : B → A` is a
section of the map `h` on top, then `t ∘ s` is a section of the map `f` on the
left.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (f : A → X) (g : B → X) (h : A → B) (H : f ~ g ∘ h) (t : section h)
  where

  map-section-left-map-triangle : section g → X → A
  map-section-left-map-triangle s = map-section-comp g h t s

  is-section-map-section-left-map-triangle :
    (s : section g) → is-section f (map-section-left-map-triangle s)
  is-section-map-section-left-map-triangle s =
    ( H ·r map-section-comp g h t s) ∙h
    ( is-section-map-section-comp g h t s)

  section-left-map-triangle : section g → section f
  pr1 (section-left-map-triangle s) = map-section-left-map-triangle s
  pr2 (section-left-map-triangle s) = is-section-map-section-left-map-triangle s
```
