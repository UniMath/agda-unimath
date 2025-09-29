# Commuting squares of maps

```agda
module foundation-core.commuting-squares-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.transposition-identifications-along-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

A square of maps

```text
            top
       A --------> X
       |           |
  left |           | right
       ∨           ∨
       B --------> Y
          bottom
```

is said to be a {{#concept "commuting square" Disambiguation="maps"}} of maps if
there is a [homotopy](foundation-core.homotopies.md)

```text
  bottom ∘ left ~ right ∘ top.
```

Such a homotopy is called the
{{#concept "coherence" Disambiguation="commuting square of maps" Agda=coherence-square-maps}}
of the commuting square.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4}
  (top : C → B) (left : C → A) (right : B → X) (bottom : A → X)
  where

  coherence-square-maps : UU (l3 ⊔ l4)
  coherence-square-maps = bottom ∘ left ~ right ∘ top

  coherence-square-maps' : UU (l3 ⊔ l4)
  coherence-square-maps' = right ∘ top ~ bottom ∘ left
```

## Properties

### Pasting commuting squares horizontally

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top-left : A → B) (top-right : B → C)
  (left : A → X) (mid : B → Y) (right : C → Z)
  (bottom-left : X → Y) (bottom-right : Y → Z)
  where

  pasting-horizontal-coherence-square-maps :
    coherence-square-maps top-left left mid bottom-left →
    coherence-square-maps top-right mid right bottom-right →
    coherence-square-maps
      (top-right ∘ top-left) left right (bottom-right ∘ bottom-left)
  pasting-horizontal-coherence-square-maps sq-left sq-right =
    (bottom-right ·l sq-left) ∙h (sq-right ·r top-left)

  pasting-horizontal-coherence-square-maps' :
    coherence-square-maps' top-left left mid bottom-left →
    coherence-square-maps' top-right mid right bottom-right →
    coherence-square-maps'
      (top-right ∘ top-left) left right (bottom-right ∘ bottom-left)
  pasting-horizontal-coherence-square-maps' sq-left sq-right =
     (sq-right ·r top-left) ∙h (bottom-right ·l sq-left)

  pasting-horizontal-up-to-htpy-coherence-square-maps :
    {top : A → C} (H : coherence-triangle-maps top top-right top-left)
    {bottom : X → Z}
    (K : coherence-triangle-maps bottom bottom-right bottom-left) →
    coherence-square-maps top-left left mid bottom-left →
    coherence-square-maps top-right mid right bottom-right →
    coherence-square-maps top left right bottom
  pasting-horizontal-up-to-htpy-coherence-square-maps H K sq-left sq-right =
    ( ( K ·r left) ∙h
      ( pasting-horizontal-coherence-square-maps sq-left sq-right)) ∙h
    ( inv-htpy (right ·l H))
```

### Pasting commuting squares vertically

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  (top : A → X)
  (left-top : A → B) (right-top : X → Y)
  (mid : B → Y)
  (left-bottom : B → C) (right-bottom : Y → Z)
  (bottom : C → Z)
  where

  pasting-vertical-coherence-square-maps :
    coherence-square-maps top left-top right-top mid →
    coherence-square-maps mid left-bottom right-bottom bottom →
    coherence-square-maps
      top (left-bottom ∘ left-top) (right-bottom ∘ right-top) bottom
  pasting-vertical-coherence-square-maps sq-top sq-bottom =
    (sq-bottom ·r left-top) ∙h (right-bottom ·l sq-top)

  pasting-vertical-up-to-htpy-coherence-square-maps :
    {left : A → C} (H : coherence-triangle-maps left left-bottom left-top)
    {right : X → Z} (K : coherence-triangle-maps right right-bottom right-top) →
    coherence-square-maps top left-top right-top mid →
    coherence-square-maps mid left-bottom right-bottom bottom →
    coherence-square-maps top left right bottom
  pasting-vertical-up-to-htpy-coherence-square-maps H K sq-top sq-bottom =
    ( ( bottom ·l H) ∙h
      ( pasting-vertical-coherence-square-maps sq-top sq-bottom)) ∙h
    ( inv-htpy (K ·r top))
```

### Associativity of horizontal pasting

**Proof:** Consider a commuting diagram of the form

```text
        α₀       β₀       γ₀
    A -----> X -----> U -----> K
    |        |        |        |
  f |   α  g |   β  h |   γ    | i
    ∨        ∨        ∨        ∨
    B -----> Y -----> V -----> L.
        α₁       β₁       γ₁
```

Then we can make the following calculation, in which we write `□` for horizontal
pasting of squares:

```text
  (α □ β) □ γ
  ＝ (γ₁ ·l ((β₁ ·l α) ∙h (β ·r α₀))) ∙h (γ ·r (β₀ ∘ α₀))
  ＝ ((γ₁ ·l (β₁ ·l α)) ∙h (γ₁ ·l (β ·r α₀))) ∙h (γ ·r (β₀ ∘ α₀))
  ＝ ((γ₁ ∘ β₁) ·l α) ∙h (((γ₁ ·l β) ·r α₀) ∙h ((γ ·r β₀) ·r α₀))
  ＝ ((γ₁ ∘ β₁) ·l α) ∙h (((γ₁ ·l β) ∙h (γ ·r β₀)) ·r α₀)
  ＝ α □ (β □ γ)
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4} {U : UU l5} {V : UU l6}
  {K : UU l7} {L : UU l8}
  (α₀ : A → X) (β₀ : X → U) (γ₀ : U → K)
  (f : A → B) (g : X → Y) (h : U → V) (i : K → L)
  (α₁ : B → Y) (β₁ : Y → V) (γ₁ : V → L)
  (α : coherence-square-maps α₀ f g α₁)
  (β : coherence-square-maps β₀ g h β₁)
  (γ : coherence-square-maps γ₀ h i γ₁)
  where

  assoc-pasting-horizontal-coherence-square-maps :
    pasting-horizontal-coherence-square-maps
      ( β₀ ∘ α₀)
      ( γ₀)
      ( f)
      ( h)
      ( i)
      ( β₁ ∘ α₁)
      ( γ₁)
      ( pasting-horizontal-coherence-square-maps α₀ β₀ f g h α₁ β₁ α β)
      ( γ) ~
    pasting-horizontal-coherence-square-maps
      ( α₀)
      ( γ₀ ∘ β₀)
      ( f)
      ( g)
      ( i)
      ( α₁)
      ( γ₁ ∘ β₁)
      ( α)
      ( pasting-horizontal-coherence-square-maps β₀ γ₀ g h i β₁ γ₁ β γ)
  assoc-pasting-horizontal-coherence-square-maps a =
    ( ap
      ( _∙ _)
      ( ( ap-concat γ₁ (ap β₁ (α a)) (β (α₀ a))) ∙
        ( inv (ap (_∙ _) (ap-comp γ₁ β₁ (α a)))))) ∙
    ( assoc (ap (γ₁ ∘ β₁) (α a)) (ap γ₁ (β (α₀ a))) (γ (β₀ (α₀ a))))
```

### The unit laws for horizontal pasting of commuting squares of maps

#### The left unit law

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : A → X) (f : A → B) (g : X → Y) (j : B → Y)
  (α : coherence-square-maps i f g j)
  where

  left-unit-law-pasting-horizontal-coherence-square-maps :
    pasting-horizontal-coherence-square-maps id i f f g id j refl-htpy α ~ α
  left-unit-law-pasting-horizontal-coherence-square-maps = refl-htpy
```

### The right unit law

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (i : A → X) (f : A → B) (g : X → Y) (j : B → Y)
  (α : coherence-square-maps i f g j)
  where

  right-unit-law-pasting-horizontal-coherence-square-maps :
    pasting-horizontal-coherence-square-maps i id f g g j id α refl-htpy ~ α
  right-unit-law-pasting-horizontal-coherence-square-maps a =
    right-unit ∙ ap-id (α a)
```

### Inverting squares horizontally and vertically

If the horizontal/vertical maps in a commuting square are both
[equivalences](foundation-core.equivalences.md), then the square remains
commuting if we invert those equivalences.

```agda
horizontal-inv-equiv-coherence-square-maps :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A → X) (right : B → Y) (bottom : X ≃ Y) →
  coherence-square-maps (map-equiv top) left right (map-equiv bottom) →
  coherence-square-maps (map-inv-equiv top) right left (map-inv-equiv bottom)
horizontal-inv-equiv-coherence-square-maps top left right bottom H b =
  map-eq-transpose-equiv-inv
    ( bottom)
    ( ( ap right (inv (is-section-map-inv-equiv top b))) ∙
      ( inv (H (map-inv-equiv top b))))

vertical-inv-equiv-coherence-square-maps :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A → B) (left : A ≃ X) (right : B ≃ Y) (bottom : X → Y) →
  coherence-square-maps top (map-equiv left) (map-equiv right) bottom →
  coherence-square-maps bottom (map-inv-equiv left) (map-inv-equiv right) top
vertical-inv-equiv-coherence-square-maps top left right bottom H x =
  map-eq-transpose-equiv
    ( right)
    ( ( inv (H (map-inv-equiv left x))) ∙
      ( ap bottom (is-section-map-inv-equiv left x)))

coherence-square-maps-inv-equiv :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (top : A ≃ B) (left : A ≃ X) (right : B ≃ Y) (bottom : X ≃ Y) →
  coherence-square-maps
    ( map-equiv top)
    ( map-equiv left)
    ( map-equiv right)
    ( map-equiv bottom) →
  coherence-square-maps
    ( map-inv-equiv bottom)
    ( map-inv-equiv right)
    ( map-inv-equiv left)
    ( map-inv-equiv top)
coherence-square-maps-inv-equiv top left right bottom H =
  vertical-inv-equiv-coherence-square-maps
    ( map-inv-equiv top)
    ( right)
    ( left)
    ( map-inv-equiv bottom)
    ( horizontal-inv-equiv-coherence-square-maps
      ( top)
      ( map-equiv left)
      ( map-equiv right)
      ( bottom)
      ( H))
```

## See also

Several structures make essential use of commuting squares of maps:

- [Cones over cospan diagrams](foundation.cones-over-cospan-diagrams.md)
- [Cocones under span diagrams](synthetic-homotopy-theory.cocones-under-spans.md)
- [Morphisms of arrows](foundation.morphisms-arrows.md)
