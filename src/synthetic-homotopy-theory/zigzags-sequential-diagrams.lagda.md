# Zigzags between sequential diagrams

```agda
module synthetic-homotopy-theory.zigzags-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.retractions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.shifts-sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A
{{#concept "zigzag" Disambiguation="sequential diagrams" Agda=zigzag-sequential-diagram}}
between [sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)` and `(B, b)` is a pair of families of maps

```text
  fₙ : Aₙ → Bₙ
  gₙ : Bₙ → Aₙ₊₁
```

and [coherences](foundation-core.commuting-triangles-of-maps.md) between them,
such that they fit in the following diagram:

```text
       a₀        a₁
  A₀ -----> A₁ -----> A₂ -----> ⋯
   \       ∧ \       ∧
    \     /   \ f₁  /
  f₀ \   / g₀  \   / g₁
      ∨ /       ∨ /
      B₀ -----> B₁ -----> ⋯ .
           b₀
```

Given [colimits](synthetic-homotopy-theory.sequential-colimits.md) `X` of `A`
and `Y` of `B`, the zigzag induces maps `f∞ : X → Y` and `g∞ : Y → X`, which we
show to be mutually inverse [equivalences](foundation-core.equivalences.md).

## Definitions

### A zigzag between sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  module _
    (f :
      (n : ℕ) →
      family-sequential-diagram A n → family-sequential-diagram B n)
    (g :
      (n : ℕ) →
      family-sequential-diagram B n → family-sequential-diagram A (succ-ℕ n))
    where

    coherence-upper-triangle-zigzag-sequential-diagram : UU l1
    coherence-upper-triangle-zigzag-sequential-diagram =
      (n : ℕ) →
      coherence-triangle-maps
        ( map-sequential-diagram A n)
        ( g n)
        ( f n)

    coherence-lower-triangle-zigzag-sequential-diagram : UU l2
    coherence-lower-triangle-zigzag-sequential-diagram =
      (n : ℕ) →
      coherence-triangle-maps
        ( map-sequential-diagram B n)
        ( f (succ-ℕ n))
        ( g n)

  zigzag-sequential-diagram : UU (l1 ⊔ l2)
  zigzag-sequential-diagram =
    Σ ( (n : ℕ) →
        family-sequential-diagram A n → family-sequential-diagram B n)
      ( λ f →
        Σ ( (n : ℕ) →
            family-sequential-diagram B n →
            family-sequential-diagram A (succ-ℕ n))
          ( λ g →
            coherence-upper-triangle-zigzag-sequential-diagram f g ×
            coherence-lower-triangle-zigzag-sequential-diagram f g))
```

### Components of a zigzag of sequential diagrams

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagram A B)
  where

  map-zigzag-sequential-diagram :
    (n : ℕ) →
    family-sequential-diagram A n → family-sequential-diagram B n
  map-zigzag-sequential-diagram = pr1 z

  inv-map-zigzag-sequential-diagram :
    (n : ℕ) →
    family-sequential-diagram B n → family-sequential-diagram A (succ-ℕ n)
  inv-map-zigzag-sequential-diagram = pr1 (pr2 z)

  upper-triangle-zigzag-sequential-diagram :
    coherence-upper-triangle-zigzag-sequential-diagram A B
      ( map-zigzag-sequential-diagram)
      ( inv-map-zigzag-sequential-diagram)
  upper-triangle-zigzag-sequential-diagram = pr1 (pr2 (pr2 z))

  lower-triangle-zigzag-sequential-diagram :
    coherence-lower-triangle-zigzag-sequential-diagram A B
      ( map-zigzag-sequential-diagram)
      ( inv-map-zigzag-sequential-diagram)
  lower-triangle-zigzag-sequential-diagram = pr2 (pr2 (pr2 z))
```

### Half-shifts of zigzags of sequential diagrams

We can forget the first triangle of a zigzag between `(A, a)` and `(B, b)` to
get a zigzag between `(B, b)` and the
[shift](synthetic-homotopy-theory.shifts-sequential-diagrams.md) `(A[1], a[1])`

```text
       b₀        b₁
  B₀ -----> B₁ -----> B₂ -----> ⋯
   \       ∧ \       ∧
    \     /   \ g₁  /
  g₀ \   / f₁  \   / f₂
      ∨ /       ∨ /
      A₁ -----> A₂ -----> ⋯ .
           a₁
```

We call this a _half-shift_ of the original zigzag, and it provides a symmetry
between the downward-going `f` maps and upward-going `g` maps. We exploit this
symmetry in the proceeding constructions by formulating the definitions and
lemmas for the downwards directions, and then applying them to the half-shift of
a zigzag to get the constructions for the upward direction.

Repeating a half-shift twice gets us a shift of a zigzag.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagram A B)
  where

  half-shift-zigzag-sequential-diagram :
    zigzag-sequential-diagram B (shift-once-sequential-diagram A)
  pr1 half-shift-zigzag-sequential-diagram =
    inv-map-zigzag-sequential-diagram z
  pr1 (pr2 half-shift-zigzag-sequential-diagram) n =
    map-zigzag-sequential-diagram z (succ-ℕ n)
  pr1 (pr2 (pr2 half-shift-zigzag-sequential-diagram)) =
    lower-triangle-zigzag-sequential-diagram z
  pr2 (pr2 (pr2 half-shift-zigzag-sequential-diagram)) n =
    upper-triangle-zigzag-sequential-diagram z (succ-ℕ n)

module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagram A B)
  where

  shift-zigzag-sequential-diagram :
    zigzag-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( shift-once-sequential-diagram B)
  shift-zigzag-sequential-diagram =
    half-shift-zigzag-sequential-diagram
      ( half-shift-zigzag-sequential-diagram z)
```

### Morphisms of sequential diagrams induced by zigzags of sequential diagrams

We can realign a zigzag

```text
       a₀        a₁
  A₀ -----> A₁ -----> A₂ -----> ⋯
   \       ∧ \       ∧
    \     /   \ f₁  /
  f₀ \   / g₀  \   / g₁
      ∨ /       ∨ /
      B₀ -----> B₁ -----> ⋯
           b₀
```

into a [morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`f : A → B`

```text
          a₀        a₁
     A₀ -----> A₁ -----> A₂ -----> ⋯
     |        ∧|        ∧|
  f₀ |   g₀ /  | f₁   /  | f₂
     |    /    |    / g₁ |
     ∨  /      ∨  /      ∨
     B₀ -----> B₁ -----> B₂ -----> ⋯ .
          b₀        b₁
```

Similarly, we can realign the half-shift of a zigzag to get the morphism
`g : B → A[1]`:

```text
          b₀        b₁
     B₀ -----> B₁ -----> B₂ -----> ⋯
     |        ∧|        ∧|
  g₀ |   f₁ /  | g₁   /  | g₂
     |    /    |    / f₂ |
     ∨  /      ∨  /      ∨
     A₁ -----> A₂ -----> A₃ -----> ⋯ ,
          a₁        a₂
```

which should be thought of as an inverse of `f` --- and we show that it indeed
induces an inverse in the colimit further down.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagram A B)
  where

  naturality-map-hom-diagram-zigzag-sequential-diagram :
    naturality-hom-sequential-diagram A B (map-zigzag-sequential-diagram z)
  naturality-map-hom-diagram-zigzag-sequential-diagram n =
    horizontal-pasting-up-diagonal-coherence-triangle-maps
      ( map-sequential-diagram A n)
      ( map-zigzag-sequential-diagram z n)
      ( map-zigzag-sequential-diagram z (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n))
      ( lower-triangle-zigzag-sequential-diagram z n)

  hom-diagram-zigzag-sequential-diagram : hom-sequential-diagram A B
  pr1 hom-diagram-zigzag-sequential-diagram =
    map-zigzag-sequential-diagram z
  pr2 hom-diagram-zigzag-sequential-diagram =
    naturality-map-hom-diagram-zigzag-sequential-diagram

module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagram A B)
  where

  inv-hom-diagram-zigzag-sequential-diagram :
    hom-sequential-diagram B (shift-once-sequential-diagram A)
  inv-hom-diagram-zigzag-sequential-diagram =
    hom-diagram-zigzag-sequential-diagram
      ( half-shift-zigzag-sequential-diagram z)
```

### Zigzags of sequential diagrams unfold to the shifting morphism of sequential diagrams

After composing the morphisms induced by a zigzag, we get a morphism
`g ∘ f : A → A[1]`

```text
          a₀        a₁
     A₀ -----> A₁ -----> A₂ -----> ⋯
     |        ∧|        ∧|
  f₀ |   g₀ /  | f₁   /  | f₂
     |    /    |    / g₁ |
     ∨  / b₀   ∨  / b₁   ∨
     B₀ -----> B₁ -----> B₂ -----> ⋯
     |        ∧|        ∧|
  g₀ |   f₁ /  | g₁   /  | g₂
     |    /    |    / f₂ |
     ∨  /      ∨  /      ∨
     A₁ -----> A₂ -----> A₃ -----> ⋯ .
          a₁        a₂
```

We show that there is a
[homotopy](synthetic-homotopy-theory.morphisms-sequential-diagrams.md) between
this morphism and the
[shift inclusion morphism](synthetic-homotopy-theory.shifts-sequential-diagrams.md)
`a : A → A[1]`

```text
        a₀      a₁
    A₀ ---> A₁ ---> A₂ ---> ⋯
    |       |       |
 a₀ |       | a₁    | a₂
    ∨       ∨       ∨
    A₁ ---> A₂ ---> A₃ ---> ⋯ .
        a₁      a₂
```

**Proof:** Component-wise the homotopies `aₙ ~ gₙ ∘ fₙ` are given by the upper
triangles in the zigzag. The coherence of a homotopy requires us to show that
the compositions

```text
      aₙ
  Aₙ ----> Aₙ₊₁
            | \ fₙ₊₁
            |   ∨
       aₙ₊₁ |    Bₙ₊₁
            |   /
            ∨ ∨ gₙ₊₁
           Aₙ₊₂
```

and

```text
               aₙ
          Aₙ -----> Aₙ₊₁
        /  |        ∧|
      / fₙ |   gₙ /  | fₙ₊₁
     |     |    /    |
     |     ∨  /      ∨
  aₙ |    Bₙ -----> Bₙ₊₁
     |     |        ∧|
     |  gₙ | fₙ₊₁ /  | gₙ₊₁
       \   |    /    |
         ∨ ∨  /      ∨
          Aₙ₊₁ ---> Aₙ₊₂
               aₙ₊₁
```

are homotopic. Since the skewed square

```text
         gₙ
    Bₙ -----> Aₙ₊₁
     |         |
  gₙ |         | fₙ₊₁
     ∨         ∨
    Aₙ₊₁ ---> Bₙ₊₁
         fₙ₊₁
```

in the middle is composed of inverse triangles, it is homotopic to the
reflexivity homotopy, which makes the second diagram collapse to

```text
           aₙ
        --------
      /          \
    /              ∨
  Aₙ ----> Bₙ ----> Aₙ₊₁
    \ fₙ       gₙ  ∧ |   \ fₙ₊₁
      \          /   |     ∨
        --------     | aₙ₊₁ Bₙ₊₁
           aₙ        |     /
                     ∨   ∨ gₙ₊₁
                    Aₙ₊₂ ,
```

where the globe is again composed of inverse triangles, so the diagram collapses
to

```text
      aₙ
  Aₙ ----> Aₙ₊₁
            | \ fₙ₊₁
            |   ∨
       aₙ₊₁ |    Bₙ₊₁
            |   /
            ∨ ∨ gₙ₊₁
           Aₙ₊₂ ,
```

which is what we needed to show.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  (z : zigzag-sequential-diagram A B)
  where

  htpy-hom-shift-hom-zigzag-sequential-diagram :
    htpy-hom-sequential-diagram
      ( shift-once-sequential-diagram A)
      ( hom-shift-once-sequential-diagram A)
      ( comp-hom-sequential-diagram A B
        ( shift-once-sequential-diagram A)
        ( inv-hom-diagram-zigzag-sequential-diagram z)
        ( hom-diagram-zigzag-sequential-diagram z))
  pr1 htpy-hom-shift-hom-zigzag-sequential-diagram =
    upper-triangle-zigzag-sequential-diagram z
  pr2 htpy-hom-shift-hom-zigzag-sequential-diagram n =
    inv-concat-right-homotopy-coherence-square-homotopies
      ( ( map-sequential-diagram A (succ-ℕ n)) ·l
        ( upper-triangle-zigzag-sequential-diagram z n))
      ( refl-htpy)
      ( naturality-comp-hom-sequential-diagram A B
        ( shift-once-sequential-diagram A)
        ( inv-hom-diagram-zigzag-sequential-diagram z)
        ( hom-diagram-zigzag-sequential-diagram z)
        ( n))
      ( ( upper-triangle-zigzag-sequential-diagram z (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( pasting-coherence-squares-collapse-triangles
        ( map-sequential-diagram A n)
        ( map-zigzag-sequential-diagram z n)
        ( map-zigzag-sequential-diagram z (succ-ℕ n))
        ( map-sequential-diagram B n)
        ( inv-map-zigzag-sequential-diagram z n)
        ( inv-map-zigzag-sequential-diagram z (succ-ℕ n))
        ( map-sequential-diagram A (succ-ℕ n))
        ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n))
        ( lower-triangle-zigzag-sequential-diagram z n)
        ( inv-htpy (lower-triangle-zigzag-sequential-diagram z n))
        ( upper-triangle-zigzag-sequential-diagram z (succ-ℕ n))
        ( left-inv-htpy (lower-triangle-zigzag-sequential-diagram z n)))
      ( right-whisker-concat-coherence-square-homotopies
        ( ( map-sequential-diagram A (succ-ℕ n)) ·l
          ( upper-triangle-zigzag-sequential-diagram z n))
        ( refl-htpy)
        ( ( map-sequential-diagram A (succ-ℕ n)) ·l
          ( inv-htpy (upper-triangle-zigzag-sequential-diagram z n)))
        ( refl-htpy)
        ( inv-htpy
          ( right-inv-htpy-left-whisker
            ( map-sequential-diagram A (succ-ℕ n))
            ( upper-triangle-zigzag-sequential-diagram z n)))
        ( ( upper-triangle-zigzag-sequential-diagram z (succ-ℕ n)) ·r
          ( map-sequential-diagram A n)))
```

## Properties

### Zigzags of sequential diagrams induce equivalences of sequential colimits

By
[functoriality](synthetic-homotopy-theory.functoriality-sequential-colimits.md)
of sequential colimits, the morphism `f : A → B` induced by a zigzag then
induces a map of colimits `A∞ → B∞`. We show that this induced map is an
equivalence.

**Proof:** Given a colimit `X` of `(A, a)` and a colimit `Y` of `(B, b)`, we get
a map `f∞ : X → Y`. Since `X` is also a colimit of `(A[1], a[1])`, the morphism
`g : B → A[1]` induces a map `g∞ : Y → X`. Composing the two, we get
`g∞ ∘ f∞ : X → X`. By functoriality, this map is homotopic to `(g ∘ f)∞`, and
taking a colimit preserves homotopies, so `g ∘ f ~ a` implies `(g ∘ f)∞ ~ a∞`.
In
[`shifts-sequential-diagrams`](synthetic-homotopy-theory.shifts-sequential-diagrams.md)
we show that `a∞ ~ id`, so we get a commuting triangle

```text
        id
     X ---> X
     |     ∧
  f∞ |   / g∞
     ∨ /
     Y .
```

Applying this construction to the half-shift of the zigzag, we get a commuting
triangle

```text
        id
     Y ---> Y
     |     ∧
  g∞ |   / f[1]∞
     ∨ /
     X .
```

These triangles compose to the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
         id
     X -----> X
     |       ∧|
  f∞ |  g∞ /  | f[1]∞
     |   /    |
     ∨ /      ∨
     Y -----> Y .
         id
```

Since the horizontal maps are identities, we get that `g∞` is by definition an
equivalence, because we just presented its section `f∞` and its retraction
`f[1]∞`. Since `f∞` is a section of an equivalence, it is itself an equivalence.

Additionally we get the judgmental equalities `f∞⁻¹ ≐ g∞` and `g∞⁻¹ ≐ f∞`.

```agda
module _
  {l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (z : zigzag-sequential-diagram A B)
  where

  map-colimit-zigzag-sequential-diagram : X → Y
  map-colimit-zigzag-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram
      ( up-c)
      ( c')
      ( hom-diagram-zigzag-sequential-diagram z)

  inv-map-colimit-zigzag-sequential-diagram : Y → X
  inv-map-colimit-zigzag-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram
      ( up-c')
      ( shift-once-cocone-sequential-diagram c)
      ( inv-hom-diagram-zigzag-sequential-diagram z)

  upper-triangle-colimit-zigzag-sequential-diagram :
    coherence-triangle-maps
      ( id)
      ( inv-map-colimit-zigzag-sequential-diagram)
      ( map-colimit-zigzag-sequential-diagram)
  upper-triangle-colimit-zigzag-sequential-diagram =
    ( inv-htpy (compute-map-colimit-hom-shift-once-sequential-diagram up-c)) ∙h
    ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-c
      ( shift-once-cocone-sequential-diagram c)
      ( htpy-hom-shift-hom-zigzag-sequential-diagram z)) ∙h
    ( preserves-comp-map-sequential-colimit-hom-sequential-diagram
      ( up-c)
      ( up-c')
      ( shift-once-cocone-sequential-diagram c)
      ( inv-hom-diagram-zigzag-sequential-diagram z)
      ( hom-diagram-zigzag-sequential-diagram z))

  is-retraction-inv-map-colimit-zigzag-sequential-diagram :
    is-retraction
      ( map-colimit-zigzag-sequential-diagram)
      ( inv-map-colimit-zigzag-sequential-diagram)
  is-retraction-inv-map-colimit-zigzag-sequential-diagram =
    inv-htpy upper-triangle-colimit-zigzag-sequential-diagram

module _
  {l1 l2 l3 l4 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  {X : UU l3} {c : cocone-sequential-diagram A X}
  (up-c : universal-property-sequential-colimit c)
  {Y : UU l4} {c' : cocone-sequential-diagram B Y}
  (up-c' : universal-property-sequential-colimit c')
  (z : zigzag-sequential-diagram A B)
  where

  lower-triangle-colimit-zigzag-sequential-diagram :
    coherence-triangle-maps
      ( id)
      ( map-colimit-zigzag-sequential-diagram
        ( up-shift-cocone-sequential-diagram 1 up-c)
        ( up-shift-cocone-sequential-diagram 1 up-c')
        ( shift-zigzag-sequential-diagram z))
      ( map-colimit-zigzag-sequential-diagram up-c'
        ( up-shift-cocone-sequential-diagram 1 up-c)
        ( half-shift-zigzag-sequential-diagram z))
  lower-triangle-colimit-zigzag-sequential-diagram =
    upper-triangle-colimit-zigzag-sequential-diagram
      ( up-c')
      ( up-shift-cocone-sequential-diagram 1 up-c)
      ( half-shift-zigzag-sequential-diagram z)

  is-equiv-inv-map-colimit-zigzag-sequential-diagram :
    is-equiv (inv-map-colimit-zigzag-sequential-diagram up-c up-c' z)
  pr1 is-equiv-inv-map-colimit-zigzag-sequential-diagram =
    ( map-colimit-zigzag-sequential-diagram up-c up-c' z) ,
    ( is-retraction-inv-map-colimit-zigzag-sequential-diagram up-c up-c' z)
  pr2 is-equiv-inv-map-colimit-zigzag-sequential-diagram =
    ( map-colimit-zigzag-sequential-diagram
      ( up-shift-cocone-sequential-diagram 1 up-c)
      ( up-shift-cocone-sequential-diagram 1 up-c')
      ( shift-zigzag-sequential-diagram z)) ,
    ( is-retraction-inv-map-colimit-zigzag-sequential-diagram
      ( up-c')
      ( up-shift-cocone-sequential-diagram 1 up-c)
      ( half-shift-zigzag-sequential-diagram z))

  inv-equiv-colimit-zigzag-sequential-diagram : Y ≃ X
  pr1 inv-equiv-colimit-zigzag-sequential-diagram =
    inv-map-colimit-zigzag-sequential-diagram up-c up-c' z
  pr2 inv-equiv-colimit-zigzag-sequential-diagram =
    is-equiv-inv-map-colimit-zigzag-sequential-diagram

  equiv-colimit-zigzag-sequential-diagram : X ≃ Y
  pr1 equiv-colimit-zigzag-sequential-diagram =
    map-colimit-zigzag-sequential-diagram up-c up-c' z
  pr2 equiv-colimit-zigzag-sequential-diagram =
    is-equiv-map-inv-equiv inv-equiv-colimit-zigzag-sequential-diagram
```
