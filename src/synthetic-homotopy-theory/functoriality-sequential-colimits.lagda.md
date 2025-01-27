# Functoriality of sequential colimits

```agda
module synthetic-homotopy-theory.functoriality-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.commuting-prisms-of-maps
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.retracts-of-sequential-diagrams
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

Given two
[sequential diagrams](synthetic-homotopy-theory.sequential-diagrams.md) `(A, a)`
and `(B, b)`, their
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
`X` and `Y`, and a
[morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`f : (A, a) → (B, b)`, there is a unique map `g : X → Y`, such that the diagram

```text
        a₀      a₁      a₂
    A₀ ---> A₁ ---> A₂ ---> ⋯ ---> X
    |       |       |              |
 f₀ |       | f₁    | f₂           | g
    ∨       ∨       ∨              ∨
    B₀ ---> B₁ ---> B₂ ---> ⋯ ---> Y
        b₀      b₁      b₂
```

[commutes](foundation.commuting-squares-of-maps.md).

The unique map corresponding to the identity morphism is the identity map
`id : X → X`, and the unique map corresponding to a composite of two morphisms
is the composite of the two unique maps for the individual morphisms.

In particular, when we also consider existence of the
[standard sequential colimits](synthetic-homotopy-theory.sequential-colimits.md),
we obtain a functorial action taking sequential diagrams and morphisms between
them to their colimits and maps between them.

```text
  (A, a)    A∞
    |       |
  f |   ↦   | f∞
    ∨       ∨
  (B, b)    B∞  .
```

Additionally, an
[equivalence of sequential diagrams](synthetic-homotopy-theory.equivalences-sequential-diagrams.md)
induces an [equivalence](foundation.equivalences.md) of their colimits.

## Properties

### A morphism of sequential diagrams induces a map of cocones

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( f : hom-sequential-diagram A B) {X : UU l3}
  where

  map-cocone-hom-sequential-diagram :
    cocone-sequential-diagram B X → cocone-sequential-diagram A X
  map-cocone-hom-sequential-diagram c =
    comp-hom-sequential-diagram A B (constant-sequential-diagram X) c f
```

### A morphism of sequential diagrams induces a map of sequential colimits

The unique map `g : X → Y` such that the diagram

```text
        a₀      a₁      a₂
    A₀ ---> A₁ ---> A₂ ---> ⋯ ---> X
    |       |       |              |
 f₀ |       | f₁    | f₂           | g
    ∨       ∨       ∨              ∨
    B₀ ---> B₁ ---> B₂ ---> ⋯ ---> Y
        b₀      b₁      b₂
```

commutes then induces a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) under
`(A, a)` with codomain `Y`, which is homotopic to the cocone under `(B, b)`
precomposed by `f`.

This homotopy of cocones provides
[vertical commuting prisms of maps](foundation.commuting-prisms-of-maps.md),

```text
          Aₙ₊₁
         ∧ | \
       /   |   \
     /     |fₙ₊₁ ∨
    Aₙ ---------> X
    |      |      |
    |      ∨      |
 fₙ |     Bₙ₊₁    | f∞
    |    ∧   \    |
    |  /       \  |
    ∨/           ∨∨
    Bₙ ---------> Y ,
```

where the [triangles](foundation-core.commuting-triangles-of-maps.md) are
coherences of the cocones of the sequential colimits, the back left
[square](foundation-core.commuting-triangles-of-maps.md) is coherence of `f`,
and the front and back right squares are provided by uniqueness of `g`.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { X : UU l3} {c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { Y : UU l4} (c' : cocone-sequential-diagram B Y)
  ( f : hom-sequential-diagram A B)
  where

  map-sequential-colimit-hom-sequential-diagram : X → Y
  map-sequential-colimit-hom-sequential-diagram =
    map-universal-property-sequential-colimit up-c
      ( map-cocone-hom-sequential-diagram f c')

  htpy-cocone-map-sequential-colimit-hom-sequential-diagram :
    htpy-cocone-sequential-diagram
      ( cocone-map-sequential-diagram c
        ( map-sequential-colimit-hom-sequential-diagram))
      ( map-cocone-hom-sequential-diagram f c')
  htpy-cocone-map-sequential-colimit-hom-sequential-diagram =
    htpy-cocone-universal-property-sequential-colimit up-c
      ( map-cocone-hom-sequential-diagram f c')

  htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram :
    ( n : ℕ) →
    coherence-square-maps
      ( map-hom-sequential-diagram B f n)
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c' n)
      ( map-sequential-colimit-hom-sequential-diagram)
  htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram =
    htpy-htpy-cocone-sequential-diagram
      ( htpy-cocone-map-sequential-colimit-hom-sequential-diagram)

  coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram :
    ( n : ℕ) →
    coherence-square-homotopies
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram n)
      ( ( map-sequential-colimit-hom-sequential-diagram) ·l
        ( coherence-cocone-sequential-diagram c n))
      ( coherence-cocone-sequential-diagram
        ( map-cocone-hom-sequential-diagram f c')
        ( n))
      ( ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
  coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram =
    coherence-htpy-htpy-cocone-sequential-diagram
      htpy-cocone-map-sequential-colimit-hom-sequential-diagram

  prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagram :
    ( n : ℕ) →
    vertical-coherence-prism-maps
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-sequential-diagram c' n)
      ( map-cocone-sequential-diagram c' (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-sequential-colimit-hom-sequential-diagram)
      ( coherence-cocone-sequential-diagram c n)
      ( inv-htpy
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram n))
      ( inv-htpy
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( succ-ℕ n)))
      ( naturality-map-hom-sequential-diagram B f n)
      ( coherence-cocone-sequential-diagram c' n)
  prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagram n =
    rotate-vertical-coherence-prism-maps
      ( map-cocone-sequential-diagram c n)
      ( map-cocone-sequential-diagram c (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-sequential-diagram c' n)
      ( map-cocone-sequential-diagram c' (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-sequential-colimit-hom-sequential-diagram)
      ( coherence-cocone-sequential-diagram c n)
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram n)
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
        ( succ-ℕ n))
      ( naturality-map-hom-sequential-diagram B f n)
      ( coherence-cocone-sequential-diagram c' n)
      ( inv-htpy
        ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( n)))
```

### Homotopies between morphisms of sequential diagrams induce homotopies of corresponding maps between sequential colimits

```agda
module _
  { l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { X : UU l3} {c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { Y : UU l4} (c' : cocone-sequential-diagram B Y)
  { f g : hom-sequential-diagram A B} (H : htpy-hom-sequential-diagram B f g)
  where

  htpy-map-sequential-colimit-htpy-hom-sequential-diagram :
    map-sequential-colimit-hom-sequential-diagram up-c c' f ~
    map-sequential-colimit-hom-sequential-diagram up-c c' g
  htpy-map-sequential-colimit-htpy-hom-sequential-diagram =
    htpy-eq
      ( ap
        ( map-sequential-colimit-hom-sequential-diagram up-c c')
        ( eq-htpy-sequential-diagram _ _ f g H))
```

### The identity morphism induces the identity map

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  where

  htpy-preserves-id-map-sequential-colimit-hom-sequential-diagram :
    htpy-out-of-sequential-colimit c
      ( map-sequential-colimit-hom-sequential-diagram up-c c
        ( id-hom-sequential-diagram A))
      ( id)
  pr1 htpy-preserves-id-map-sequential-colimit-hom-sequential-diagram =
    htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c
      ( id-hom-sequential-diagram A)
  pr2 htpy-preserves-id-map-sequential-colimit-hom-sequential-diagram n =
    ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c
      ( id-hom-sequential-diagram A)
      ( n)) ∙h
    ( ap-concat-htpy _
      ( ( right-unit-htpy) ∙h
        ( inv-htpy
          ( left-unit-law-left-whisker-comp
            ( coherence-cocone-sequential-diagram c n)))))

  preserves-id-map-sequential-colimit-hom-sequential-diagram :
    ( map-sequential-colimit-hom-sequential-diagram up-c c
      ( id-hom-sequential-diagram A)) ~
    ( id)
  preserves-id-map-sequential-colimit-hom-sequential-diagram =
    htpy-htpy-out-of-sequential-colimit up-c
      ( htpy-preserves-id-map-sequential-colimit-hom-sequential-diagram)
```

### Composition of morphisms induces composition of functions

```agda
module _
  { l1 l2 l3 l4 l5 l6 : Level}
  { A : sequential-diagram l1} {B : sequential-diagram l2}
  { C : sequential-diagram l3}
  { X : UU l4} {c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { Y : UU l5} {c' : cocone-sequential-diagram B Y}
  ( up-c' : universal-property-sequential-colimit c')
  { Z : UU l6} (c'' : cocone-sequential-diagram C Z)
  ( g : hom-sequential-diagram B C) (f : hom-sequential-diagram A B)
  where

  htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagram :
    htpy-out-of-sequential-colimit c
      ( map-sequential-colimit-hom-sequential-diagram up-c c''
        ( comp-hom-sequential-diagram A B C g f))
      ( ( map-sequential-colimit-hom-sequential-diagram up-c' c'' g) ∘
        ( map-sequential-colimit-hom-sequential-diagram up-c c' f))
  pr1 htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagram n =
    ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c''
      ( comp-hom-sequential-diagram A B C g f)
      ( n)) ∙h
    ( pasting-vertical-coherence-square-maps
      ( map-cocone-sequential-diagram c n)
      ( map-hom-sequential-diagram B f n)
      ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
      ( map-cocone-sequential-diagram c' n)
      ( map-hom-sequential-diagram C g n)
      ( map-sequential-colimit-hom-sequential-diagram up-c' c'' g)
      ( map-cocone-sequential-diagram c'' n)
      ( inv-htpy
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c'
          ( f)
          ( n)))
      ( inv-htpy
        ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c'
          ( c'')
          ( g)
          ( n))))
  pr2 htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagram n =
    ( right-whisker-concat-coherence-square-homotopies
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c''
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( ( map-sequential-colimit-hom-sequential-diagram up-c c''
          ( comp-hom-sequential-diagram A B C g f)) ·l
        ( coherence-cocone-sequential-diagram c n))
      ( coherence-cocone-sequential-diagram
        ( map-cocone-hom-sequential-diagram
          ( comp-hom-sequential-diagram A B C g f)
          ( c''))
        ( n))
      ( ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
          ( up-c)
          ( c'')
          ( comp-hom-sequential-diagram A B C g f)
          ( succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c
        ( c'')
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( _)) ∙h
    ( ap-concat-htpy
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c''
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( ( assoc-htpy
          ( ( coherence-cocone-sequential-diagram c'' n) ·r
            ( ( map-hom-sequential-diagram C g n) ∘
              ( map-hom-sequential-diagram B f n)))
          ( map-cocone-sequential-diagram c'' (succ-ℕ n) ·l _)
          ( _)) ∙h
        ( pasting-vertical-coherence-prism-maps
          ( map-cocone-sequential-diagram c n)
          ( map-cocone-sequential-diagram c (succ-ℕ n))
          ( map-sequential-diagram A n)
          ( map-cocone-sequential-diagram c' n)
          ( map-cocone-sequential-diagram c' (succ-ℕ n))
          ( map-sequential-diagram B n)
          ( map-hom-sequential-diagram B f n)
          ( map-hom-sequential-diagram B f (succ-ℕ n))
          ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
          ( map-cocone-sequential-diagram c'' n)
          ( map-cocone-sequential-diagram c'' (succ-ℕ n))
          ( map-sequential-diagram C n)
          ( map-hom-sequential-diagram C g n)
          ( map-hom-sequential-diagram C g (succ-ℕ n))
          ( map-sequential-colimit-hom-sequential-diagram up-c' c'' g)
          ( coherence-cocone-sequential-diagram c n)
          ( inv-htpy
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
              ( up-c)
              ( c')
              ( f)
              ( n)))
          ( inv-htpy
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
              ( up-c)
              ( c')
              ( f)
              ( succ-ℕ n)))
          ( naturality-map-hom-sequential-diagram B f n)
          ( coherence-cocone-sequential-diagram c' n)
          ( inv-htpy
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
              ( up-c')
              ( c'')
              ( g)
              ( n)))
          ( inv-htpy
            ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
              ( up-c')
              ( c'')
              ( g)
              ( succ-ℕ n)))
          ( naturality-map-hom-sequential-diagram C g n)
          ( coherence-cocone-sequential-diagram c'' n)
          ( prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c
            ( c')
            ( f)
            ( n))
          ( prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
            ( up-c')
            ( c'')
            ( g)
            ( n))))) ∙h
    ( inv-htpy-assoc-htpy
      ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c''
        ( comp-hom-sequential-diagram A B C g f)
        ( n))
      ( _)
      ( ( ( map-sequential-colimit-hom-sequential-diagram up-c' c'' g) ∘
          ( map-sequential-colimit-hom-sequential-diagram up-c c' f)) ·l
        ( coherence-cocone-sequential-diagram c n)))

  preserves-comp-map-sequential-colimit-hom-sequential-diagram :
    ( map-sequential-colimit-hom-sequential-diagram up-c c''
      ( comp-hom-sequential-diagram A B C g f)) ~
    ( ( map-sequential-colimit-hom-sequential-diagram up-c' c'' g) ∘
      ( map-sequential-colimit-hom-sequential-diagram up-c c' f))
  preserves-comp-map-sequential-colimit-hom-sequential-diagram =
    htpy-htpy-out-of-sequential-colimit up-c
      ( htpy-preserves-comp-map-sequential-colimit-hom-sequential-diagram)
```

### A retract of sequential diagrams induces a retract of sequential colimits

Additionally, the underlying map of the retraction is strictly equal to the map
induced by the retraction of sequential diagrams.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { X : UU l3} {c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { Y : UU l4} {c' : cocone-sequential-diagram B Y}
  ( up-c' : universal-property-sequential-colimit c')
  ( R : A retract-of-sequential-diagram B)
  where

  map-inclusion-sequential-colimit-retract-sequential-diagram : X → Y
  map-inclusion-sequential-colimit-retract-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram up-c c'
      ( inclusion-retract-sequential-diagram A B R)

  map-sequential-colimit-retract-sequential-diagram : Y → X
  map-sequential-colimit-retract-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram up-c' c
      ( hom-retraction-retract-sequential-diagram A B R)

  abstract
    is-retraction-map-sequential-colimit-retract-sequential-diagram :
      is-retraction
        ( map-inclusion-sequential-colimit-retract-sequential-diagram)
        ( map-sequential-colimit-retract-sequential-diagram)
    is-retraction-map-sequential-colimit-retract-sequential-diagram =
      ( inv-htpy
        ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-c
          ( up-c')
          ( c)
          ( hom-retraction-retract-sequential-diagram A B R)
          ( inclusion-retract-sequential-diagram A B R))) ∙h
      ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-c c
        ( is-retraction-hom-retraction-retract-sequential-diagram A B R)) ∙h
      ( preserves-id-map-sequential-colimit-hom-sequential-diagram up-c)

  retraction-sequential-colimit-retract-sequential-diagram :
    retraction map-inclusion-sequential-colimit-retract-sequential-diagram
  pr1 retraction-sequential-colimit-retract-sequential-diagram =
    map-sequential-colimit-retract-sequential-diagram
  pr2 retraction-sequential-colimit-retract-sequential-diagram =
    is-retraction-map-sequential-colimit-retract-sequential-diagram

  retract-sequential-colimit-retract-sequential-diagram :
    X retract-of Y
  pr1 retract-sequential-colimit-retract-sequential-diagram =
    map-inclusion-sequential-colimit-retract-sequential-diagram
  pr2 retract-sequential-colimit-retract-sequential-diagram =
    retraction-sequential-colimit-retract-sequential-diagram
```

### An equivalence of sequential diagrams induces an equivalence of sequential colimits

Additionally, the underlying map of the inverse equivalence is definitionally
equal to the map induced by the inverse of the equivalence of sequential
diagrams, i.e. it is the unique map `g : Y → X` making the diagram

```text
           b₀      b₁      b₂
       B₀ ---> B₁ ---> B₂ ---> ⋯ ---> Y
       |       |       |              |
  e₀⁻¹ |       | e₁⁻¹  | e₂⁻¹         | g
       ∨       ∨       ∨              ∨
       A₀ ---> A₁ ---> A₂ ---> ⋯ ---> X
           a₀      a₁      a₂
```

commute.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { X : UU l3} {c : cocone-sequential-diagram A X}
  ( up-c : universal-property-sequential-colimit c)
  { Y : UU l4} {c' : cocone-sequential-diagram B Y}
  ( up-c' : universal-property-sequential-colimit c')
  ( e : equiv-sequential-diagram A B)
  where

  map-equiv-sequential-colimit-equiv-sequential-diagram : X → Y
  map-equiv-sequential-colimit-equiv-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram up-c c'
      ( hom-equiv-sequential-diagram B e)

  map-inv-equiv-sequential-colimit-equiv-sequential-diagram : Y → X
  map-inv-equiv-sequential-colimit-equiv-sequential-diagram =
    map-sequential-colimit-hom-sequential-diagram up-c' c
      ( hom-inv-equiv-sequential-diagram B e)

  abstract
    is-section-map-inv-equiv-sequential-colimit-equiv-sequential-diagram :
      is-section
        ( map-equiv-sequential-colimit-equiv-sequential-diagram)
        ( map-inv-equiv-sequential-colimit-equiv-sequential-diagram)
    is-section-map-inv-equiv-sequential-colimit-equiv-sequential-diagram =
      ( inv-htpy
        ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-c'
          ( up-c)
          ( c')
          ( hom-equiv-sequential-diagram B e)
          ( hom-inv-equiv-sequential-diagram B e))) ∙h
      ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-c' c'
        ( is-section-inv-equiv-sequential-diagram _ e)) ∙h
      ( preserves-id-map-sequential-colimit-hom-sequential-diagram up-c')

    is-retraction-map-inv-equiv-sequential-colimit-equiv-sequential-diagram :
      is-retraction
        ( map-equiv-sequential-colimit-equiv-sequential-diagram)
        ( map-inv-equiv-sequential-colimit-equiv-sequential-diagram)
    is-retraction-map-inv-equiv-sequential-colimit-equiv-sequential-diagram =
      is-retraction-map-sequential-colimit-retract-sequential-diagram up-c up-c'
        ( retract-equiv-sequential-diagram e)

  is-equiv-map-equiv-sequential-colimit-equiv-sequential-diagram :
    is-equiv map-equiv-sequential-colimit-equiv-sequential-diagram
  is-equiv-map-equiv-sequential-colimit-equiv-sequential-diagram =
    is-equiv-is-invertible
      ( map-inv-equiv-sequential-colimit-equiv-sequential-diagram)
      ( is-section-map-inv-equiv-sequential-colimit-equiv-sequential-diagram)
      ( is-retraction-map-inv-equiv-sequential-colimit-equiv-sequential-diagram)

  equiv-sequential-colimit-equiv-sequential-diagram : X ≃ Y
  pr1 equiv-sequential-colimit-equiv-sequential-diagram =
    map-equiv-sequential-colimit-equiv-sequential-diagram
  pr2 equiv-sequential-colimit-equiv-sequential-diagram =
    is-equiv-map-equiv-sequential-colimit-equiv-sequential-diagram
```

### Functoriality of taking the standard sequential colimit

All of the above specializes to the case where `X` is the standard sequential
colimit `A∞` and `Y` is the standard sequential colimit `B∞`. In that case, we
denote the unique map `g` corresponding to a morphism of diagrams `f` by
`f∞ : A∞ → B∞`.

#### A morphism of sequential diagrams induces a map of standard sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( f : hom-sequential-diagram A B)
  where

  map-hom-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-hom-standard-sequential-colimit =
    map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit B)
      ( f)

  htpy-cocone-map-hom-standard-sequential-colimit :
    htpy-cocone-sequential-diagram
      ( cocone-map-sequential-diagram
        ( cocone-standard-sequential-colimit A)
        ( map-hom-standard-sequential-colimit))
      ( map-cocone-hom-sequential-diagram f
        ( cocone-standard-sequential-colimit B))
  htpy-cocone-map-hom-standard-sequential-colimit =
    htpy-cocone-map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit B)
      ( f)

  htpy-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-square-maps
      ( map-hom-sequential-diagram B f n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-hom-standard-sequential-colimit)
  htpy-htpy-cocone-map-hom-standard-sequential-colimit =
    htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit B)
      ( f)

  coherence-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-square-homotopies
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit n)
      ( ( map-hom-standard-sequential-colimit) ·l
        ( coherence-cocone-standard-sequential-colimit n))
      ( coherence-cocone-sequential-diagram
          ( map-cocone-hom-sequential-diagram f
            ( cocone-standard-sequential-colimit B))
          ( n))
      ( ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
  coherence-htpy-cocone-map-hom-standard-sequential-colimit =
    coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit B)
      ( f)

  prism-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    vertical-coherence-prism-maps
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram A n)
      ( map-cocone-standard-sequential-colimit n)
      ( map-cocone-standard-sequential-colimit (succ-ℕ n))
      ( map-sequential-diagram B n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-hom-standard-sequential-colimit)
      ( coherence-cocone-standard-sequential-colimit n)
      ( inv-htpy (htpy-htpy-cocone-map-hom-standard-sequential-colimit n))
      ( inv-htpy
        ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n)))
      ( naturality-map-hom-sequential-diagram B f n)
      ( coherence-cocone-standard-sequential-colimit n)
  prism-htpy-cocone-map-hom-standard-sequential-colimit =
    prism-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit B)
      ( f)
```

#### Homotopies between morphisms of sequential diagrams induce homotopies of maps of standard sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { f g : hom-sequential-diagram A B} (H : htpy-hom-sequential-diagram B f g)
  where

  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram :
    map-hom-standard-sequential-colimit B f ~
    map-hom-standard-sequential-colimit B g
  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram =
    htpy-map-sequential-colimit-htpy-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit B)
      ( H)
```

#### The identity morphism induces the identity map on the standard sequential colimit

We have `id∞ ~ id : A∞ → A∞`.

```agda
module _
  { l1 : Level} {A : sequential-diagram l1}
  where

  preserves-id-map-hom-standard-sequential-colimit :
    ( map-hom-standard-sequential-colimit A
      ( id-hom-sequential-diagram A)) ~
    ( id)
  preserves-id-map-hom-standard-sequential-colimit =
    preserves-id-map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
```

#### Forming standard sequential colimits preserves composition of morphisms of sequential diagrams

We have `(f ∘ g)∞ ~ (f∞ ∘ g∞) : A∞ → C∞`.

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { C : sequential-diagram l3}
  ( g : hom-sequential-diagram B C) (f : hom-sequential-diagram A B)
  where

  preserves-comp-map-hom-standard-sequential-colimit :
    ( map-hom-standard-sequential-colimit C
      ( comp-hom-sequential-diagram A B C g f)) ~
    ( ( map-hom-standard-sequential-colimit C g) ∘
      ( map-hom-standard-sequential-colimit B f))
  preserves-comp-map-hom-standard-sequential-colimit =
    preserves-comp-map-sequential-colimit-hom-sequential-diagram
      ( up-standard-sequential-colimit)
      ( up-standard-sequential-colimit)
      ( cocone-standard-sequential-colimit C)
      ( g)
      ( f)
```

#### An equivalence of sequential diagrams induces an equivalence of standard sequential colimits

Additionally, the underlying map of the inverse equivalence is definitionally
equal to the map induced by the inverse of the equivalence of sequential
diagrams, i.e. `(e∞)⁻¹ = (e⁻¹)∞`.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( e : equiv-sequential-diagram A B)
  where

  map-equiv-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-equiv-standard-sequential-colimit =
    map-equiv-sequential-colimit-equiv-sequential-diagram
      ( up-standard-sequential-colimit)
      ( up-standard-sequential-colimit)
      ( e)

  map-inv-equiv-standard-sequential-colimit :
    standard-sequential-colimit B → standard-sequential-colimit A
  map-inv-equiv-standard-sequential-colimit =
    map-inv-equiv-sequential-colimit-equiv-sequential-diagram
      ( up-standard-sequential-colimit)
      ( up-standard-sequential-colimit)
      ( e)

  equiv-equiv-standard-sequential-colimit :
    standard-sequential-colimit A ≃ standard-sequential-colimit B
  equiv-equiv-standard-sequential-colimit =
    equiv-sequential-colimit-equiv-sequential-diagram
      ( up-standard-sequential-colimit)
      ( up-standard-sequential-colimit)
      ( e)
```

#### A retract of sequential diagrams induces a retract of standard sequential colimits

Additionally, the underlying map of the retraction is definitionally equal to
the map induced by the retraction of sequential diagrams.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( R : A retract-of-sequential-diagram B)
  where

  map-inclusion-retract-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-inclusion-retract-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B
      ( inclusion-retract-sequential-diagram A B R)

  map-hom-retraction-retract-standard-sequential-colimit :
    standard-sequential-colimit B → standard-sequential-colimit A
  map-hom-retraction-retract-standard-sequential-colimit =
    map-hom-standard-sequential-colimit A
      ( hom-retraction-retract-sequential-diagram A B R)

  retract-retract-standard-sequential-colimit :
    (standard-sequential-colimit A) retract-of (standard-sequential-colimit B)
  retract-retract-standard-sequential-colimit =
    retract-sequential-colimit-retract-sequential-diagram
      ( up-standard-sequential-colimit)
      ( up-standard-sequential-colimit)
      ( R)
```

## References

{{#bibliography}} {{#reference SvDR20}}
