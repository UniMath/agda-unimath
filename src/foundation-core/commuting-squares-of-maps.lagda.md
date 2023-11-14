# Commuting squares of maps

```agda
module foundation-core.commuting-squares-of-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.homotopies
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

A square of maps

```text
  A ------> X
  |         |
  |         |
  |         |
  V         V
  B ------> Y
```

is said to commute if there is a homotopy between both composites.

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
    V        V        V        V
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

### Commutativity of horizontal and vertical pasting

```agda
[i] :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} {f g h k l : A → B} →
  ( H : f ~ g) (K : g ~ h) (L : h ~ k) (M : k ~ l) →
  ( H ∙h K) ∙h (L ∙h M) ~ H ∙h (K ∙h L) ∙h M
[i] H K L M =
  ( inv-htpy-assoc-htpy (H ∙h K) L M) ∙h
  ( ap-concat-htpy' _ _ M (assoc-htpy H K L))

[ii] :
  { l1 l2 : Level} {A : UU l1} {B : UU l2} {f g h h' k l : A → B} →
  ( H : f ~ g) (K : g ~ h) (K' : g ~ h') (L : h ~ k) (L' : h' ~ k) (M : k ~ l) →
  ( α : K ∙h L ~ K' ∙h L') →
  (H ∙h K) ∙h (L ∙h M) ~ (H ∙h K') ∙h (L' ∙h M)
[ii] H K K' L L' M α =
  ( [i] H K L M) ∙h
  ( ap-concat-htpy' _ _ M (ap-concat-htpy H _ _ α)) ∙h
  ( inv-htpy ([i] H K' L' M))

[iii] :
  { l1 l2 l3 l4 l5 l6 l7 : Level} →
  { A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  { X : UU l5} {Y : UU l6} {Z : UU l7} →
  ( top : A → B) (left : A → C) (mid-top : B → D) (mid-left : C → D)
  ( mid-right : D → X) (mid-bottom : D → Y) (right : X → Z) (bottom : Y → Z)
  ( H : coherence-square-maps top left mid-top mid-left)
  ( K : coherence-square-maps mid-right mid-bottom right bottom) →
  ( ( K ·r mid-left ·r left) ∙h (right ·l mid-right ·l H)) ~
  ( bottom ·l mid-bottom ·l H) ∙h (K ·r mid-top ·r top)
[iii] top left mid-top mid-left mid-right mid-bottom right bottom H K =
  ( ap-concat-htpy
    ( K ·r mid-left ·r left)
    ( _)
    ( _)
    ( associative-left-whisk-comp right mid-right H)) ∙h
  ( htpy-swap-nat-right-htpy K H) ∙h
  ( ap-concat-htpy' _ _
    ( K ·r mid-top ·r top)
    ( inv-htpy (associative-left-whisk-comp  bottom mid-bottom H)))

module _
  { l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  { A : UU l1} {B : UU l2} {C : UU l3} {X : UU l4} {Y : UU l5} {Z : UU l6}
  { M : UU l7} {N : UU l8} {O : UU l9}
  ( top-left : A → B) (top-right : B → C)
  ( left-top : A → X) (mid-top : B → Y) (right-top : C → Z)
  ( mid-left : X → Y) (mid-right : Y → Z)
  ( left-bottom : X → M) (mid-bottom : Y → N) (right-bottom : Z → O)
  ( bottom-left : M → N) (bottom-right : N → O)
  ( sq-left-top : coherence-square-maps top-left left-top mid-top mid-left)
  ( sq-right-top : coherence-square-maps top-right mid-top right-top mid-right)
  ( sq-left-bottom :
      coherence-square-maps mid-left left-bottom mid-bottom bottom-left)
  ( sq-right-bottom :
      coherence-square-maps mid-right mid-bottom right-bottom bottom-right)
  where

  commutative-pasting-vertical-pasting-horizontal-coherence-square-maps :
    ( pasting-horizontal-coherence-square-maps
      ( top-left)
      ( top-right)
      ( left-bottom ∘ left-top)
      ( mid-bottom ∘ mid-top)
      ( right-bottom ∘ right-top)
      ( bottom-left)
      ( bottom-right)
      ( pasting-vertical-coherence-square-maps
        ( top-left)
        ( left-top)
        ( mid-top)
        ( mid-left)
        ( left-bottom)
        ( mid-bottom)
        ( bottom-left)
        ( sq-left-top)
        ( sq-left-bottom))
      ( pasting-vertical-coherence-square-maps
        ( top-right)
        ( mid-top)
        ( right-top)
        ( mid-right)
        ( mid-bottom)
        ( right-bottom)
        ( bottom-right)
        ( sq-right-top)
        ( sq-right-bottom))) ~
    ( pasting-vertical-coherence-square-maps
      ( top-right ∘ top-left)
      ( left-top)
      ( right-top)
      ( mid-right ∘ mid-left)
      ( left-bottom)
      ( right-bottom)
      ( bottom-right ∘ bottom-left)
      ( pasting-horizontal-coherence-square-maps
        ( top-left)
        ( top-right)
        ( left-top)
        ( mid-top)
        ( right-top)
        ( mid-left)
        ( mid-right)
        ( sq-left-top)
        ( sq-right-top))
      ( pasting-horizontal-coherence-square-maps
        ( mid-left)
        ( mid-right)
        ( left-bottom)
        ( mid-bottom)
        ( right-bottom)
        ( bottom-left)
        ( bottom-right)
        ( sq-left-bottom)
        ( sq-right-bottom)))
  commutative-pasting-vertical-pasting-horizontal-coherence-square-maps =
    ( ap-concat-htpy' _ _ _
      ( distributive-left-whisk-concat-htpy
        ( bottom-right)
        ( sq-left-bottom ·r left-top)
        ( mid-bottom ·l sq-left-top)) ∙h
      ( [ii]
        ( bottom-right ·l (sq-left-bottom ·r left-top))
        ( bottom-right ·l mid-bottom ·l sq-left-top)
        ( sq-right-bottom ·r mid-left ·r left-top)
        ( sq-right-bottom ·r mid-top ·r top-left)
        ( right-bottom ·l mid-right ·l sq-left-top)
        ( right-bottom ·l (sq-right-top ·r top-left))
        ( inv-htpy
          ( [iii]
            ( top-left)
            ( left-top)
            ( mid-top)
            ( mid-left)
            ( mid-right)
            ( mid-bottom)
            ( right-bottom)
            ( bottom-right)
            ( sq-left-top)
            ( sq-right-bottom))))) ∙h
      ( ap-concat-htpy _ _ _
        ( inv-htpy
          ( distributive-left-whisk-concat-htpy
            ( right-bottom)
            ( mid-right ·l sq-left-top)
            ( sq-right-top ·r top-left))))
```

## See also

Several structures make essential use of commuting squares of maps:

- [Cones over cospans](foundation.cones-over-cospans.md)
- [Cocones under spans](synthetic-homotopy-theory.cocones-under-spans.md)
- [Morphisms of arrows](foundation.morphisms-arrows.md)
