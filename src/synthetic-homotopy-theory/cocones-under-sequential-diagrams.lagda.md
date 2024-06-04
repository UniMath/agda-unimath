# Cocones under sequential diagrams

```agda
module synthetic-homotopy-theory.cocones-under-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-homotopies
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.equifibered-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A
{{#concept "cocone" Disambiguation="sequential diagram" Agda=cocone-sequential-diagram}}
under a [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)
`(A, a)` with codomain `X : 𝒰` consists of a family of maps `iₙ : A n → C` and a
family of [homotopies](foundation.homotopies.md) `Hₙ` asserting that the
triangles

```text
       aₙ
 Aₙ ------> Aₙ₊₁
   \       /
    \     /
  iₙ \   / iₙ₊₁
      ∨ ∨
       X
```

[commute](foundation.commuting-triangles-of-maps.md).

## Definitions

### Cocones under sequential diagrams

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) (X : UU l2)
  where

  cocone-sequential-diagram : UU (l1 ⊔ l2)
  cocone-sequential-diagram =
    Σ ( ( n : ℕ) → family-sequential-diagram A n → X)
      ( λ i →
        ( n : ℕ) →
        coherence-triangle-maps
          ( i n)
          ( i (succ-ℕ n))
          ( map-sequential-diagram A n))
```

### Components of cocones under sequential diagrams

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  map-cocone-sequential-diagram : (n : ℕ) → family-sequential-diagram A n → X
  map-cocone-sequential-diagram = pr1 c

  coherence-cocone-sequential-diagram :
    ( n : ℕ) →
    coherence-triangle-maps
      ( map-cocone-sequential-diagram n)
      ( map-cocone-sequential-diagram (succ-ℕ n))
      ( map-sequential-diagram A n)
  coherence-cocone-sequential-diagram = pr2 c

  first-map-cocone-sequential-diagram : family-sequential-diagram A 0 → X
  first-map-cocone-sequential-diagram = map-cocone-sequential-diagram 0
```

### Homotopies of cocones under a sequential diagram

A **homotopy** between two cocones `(X, i, H)` and `(X, j, L)` with the same
vertex consists of a [sequence](foundation.dependent-sequences.md) of
[homotopies](foundation.homotopies.md) `Kₙ : iₙ ~ jₙ` and a coherence datum
filling the "pinched cylinder" with the faces `Kₙ`, `Hₙ`, `Lₙ` and `Kₙ₊₁`.

The coherence datum may be better understood by viewing a cocone as a
[morphism](synthetic-homotopy-theory.morphisms-sequential-diagrams.md) from
`(A, a)` to the constant cocone `(n ↦ X, n ↦ id)` — the two types are strictly
equal. Then a homotopy of cocones is a regular homotopy of morphisms of
sequential diagrams.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c c' : cocone-sequential-diagram A X)
  where

  coherence-htpy-cocone-sequential-diagram :
    ( (n : ℕ) →
      map-cocone-sequential-diagram c n ~ map-cocone-sequential-diagram c' n) →
    UU (l1 ⊔ l2)
  coherence-htpy-cocone-sequential-diagram K =
    ( n : ℕ) →
    coherence-square-homotopies
      ( K n)
      ( coherence-cocone-sequential-diagram c n)
      ( coherence-cocone-sequential-diagram c' n)
      ( K (succ-ℕ n) ·r map-sequential-diagram A n)

  htpy-cocone-sequential-diagram :
    UU (l1 ⊔ l2)
  htpy-cocone-sequential-diagram =
    Σ ( ( n : ℕ) →
        ( map-cocone-sequential-diagram c n) ~
        ( map-cocone-sequential-diagram c' n))
      ( coherence-htpy-cocone-sequential-diagram)
```

### Components of a homotopy of cocones under a sequential diagram

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  { c c' : cocone-sequential-diagram A X}
  ( H : htpy-cocone-sequential-diagram c c')
  where

  htpy-htpy-cocone-sequential-diagram :
    ( n : ℕ) →
    ( map-cocone-sequential-diagram c n) ~
    ( map-cocone-sequential-diagram c' n)
  htpy-htpy-cocone-sequential-diagram = pr1 H

  coherence-htpy-htpy-cocone-sequential-diagram :
    coherence-htpy-cocone-sequential-diagram c c'
      ( htpy-htpy-cocone-sequential-diagram)
  coherence-htpy-htpy-cocone-sequential-diagram = pr2 H
```

### Inverting homotopies of cocones under sequential diagrams

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c c' : cocone-sequential-diagram A X}
  (H : htpy-cocone-sequential-diagram c c')
  where

  inv-htpy-cocone-sequential-diagram : htpy-cocone-sequential-diagram c' c
  pr1 inv-htpy-cocone-sequential-diagram n =
    inv-htpy (htpy-htpy-cocone-sequential-diagram H n)
  pr2 inv-htpy-cocone-sequential-diagram n =
    horizontal-inv-coherence-square-homotopies
      ( htpy-htpy-cocone-sequential-diagram H n)
      ( coherence-cocone-sequential-diagram c n)
      ( coherence-cocone-sequential-diagram c' n)
      ( ( htpy-htpy-cocone-sequential-diagram H (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( coherence-htpy-htpy-cocone-sequential-diagram H n)
```

### Concatenation of homotopies of cocones under a sequential diagram

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  {c c' c'' : cocone-sequential-diagram A X}
  (H : htpy-cocone-sequential-diagram c c')
  (K : htpy-cocone-sequential-diagram c' c'')
  where

  concat-htpy-cocone-sequential-diagram : htpy-cocone-sequential-diagram c c''
  pr1 concat-htpy-cocone-sequential-diagram n =
    ( htpy-htpy-cocone-sequential-diagram H n) ∙h
    ( htpy-htpy-cocone-sequential-diagram K n)
  pr2 concat-htpy-cocone-sequential-diagram n =
    horizontal-pasting-coherence-square-homotopies
      ( htpy-htpy-cocone-sequential-diagram H n)
      ( htpy-htpy-cocone-sequential-diagram K n)
      ( coherence-cocone-sequential-diagram c n)
      ( coherence-cocone-sequential-diagram c' n)
      ( coherence-cocone-sequential-diagram c'' n)
      ( ( htpy-htpy-cocone-sequential-diagram H (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( ( htpy-htpy-cocone-sequential-diagram K (succ-ℕ n)) ·r
        ( map-sequential-diagram A n))
      ( coherence-htpy-htpy-cocone-sequential-diagram H n)
      ( coherence-htpy-htpy-cocone-sequential-diagram K n)
```

### Postcomposing cocones under a sequential diagram with a map

Given a cocone `c` with vertex `X` under `(A, a)` and a map `f : X → Y`, we may
extend `c` to a cocone with vertex `Y`.

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  cocone-map-sequential-diagram :
    { l : Level} {Y : UU l} →
    ( X → Y) → cocone-sequential-diagram A Y
  pr1 (cocone-map-sequential-diagram f) n =
    f ∘ map-cocone-sequential-diagram c n
  pr2 (cocone-map-sequential-diagram f) n =
    f ·l (coherence-cocone-sequential-diagram c n)
```

### Postcomposition cocones under postcomposition sequential diagrams

```agda
module _
  { l1 l2 l3 : Level} (X : UU l1) (A : sequential-diagram l2) {Y : UU l3}
  ( c : cocone-sequential-diagram A Y)
  where

  cocone-postcomp-sequential-diagram :
    cocone-sequential-diagram (postcomp-sequential-diagram X A) (X → Y)
  pr1 cocone-postcomp-sequential-diagram n g x =
    map-cocone-sequential-diagram c n (g x)
  pr2 cocone-postcomp-sequential-diagram n g =
    htpy-postcomp X (coherence-cocone-sequential-diagram c n) g
```

### Equifibered sequential diagrams induced by type families over cocones under sequential diagrams

Given a sequential diagram `(A, a)` and a cocone `c` under it with vertex `X`,
and a type family `P : X → 𝒰`, we may compose them together to get

```text
       aₙ
 Aₙ ------> Aₙ₊₁
   \       /
    \  Hₙ /
  iₙ \   / iₙ₊₁
      ∨ ∨
       X
       | P
       ∨
       𝒰 ,
```

which gives us a collection of type families `Pₙ : Aₙ → 𝒰`, and a collection of
equivalences `Pₙ a ≃ Pₙ₊₁ (aₙ a)` induced by
[transporting](foundation-core.transport-along-identifications.md) in `P` along
`Hₙ`. This data comes together to form an
[equifibered sequential diagram](synthetic-homotopy-theory.equifibered-sequential-diagrams.md)
over `A`.

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  (P : X → UU l3)
  where

  equifibered-sequential-diagram-family-cocone :
    equifibered-sequential-diagram A l3
  pr1 equifibered-sequential-diagram-family-cocone n a =
    P (map-cocone-sequential-diagram c n a)
  pr2 equifibered-sequential-diagram-family-cocone n a =
    equiv-tr P (coherence-cocone-sequential-diagram c n a)

  dependent-sequential-diagram-family-cocone : dependent-sequential-diagram A l3
  dependent-sequential-diagram-family-cocone =
    dependent-sequential-diagram-equifibered-sequential-diagram
      ( equifibered-sequential-diagram-family-cocone)

  is-equifibered-dependent-sequential-diagram-family-cocone :
    is-equifibered-dependent-sequential-diagram
      ( dependent-sequential-diagram-family-cocone)
  is-equifibered-dependent-sequential-diagram-family-cocone =
    is-equifibered-dependent-sequential-diagram-equifibered-sequential-diagram
      ( equifibered-sequential-diagram-family-cocone)
```

## Properties

### Characterization of identity types of cocones under sequential diagrams

[Equality](foundation.identity-types.md) of cocones with the same vertex is
captured by a homotopy between them.

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  refl-htpy-cocone-sequential-diagram :
    htpy-cocone-sequential-diagram c c
  pr1 refl-htpy-cocone-sequential-diagram n = refl-htpy
  pr2 refl-htpy-cocone-sequential-diagram n = right-unit-htpy

  htpy-eq-cocone-sequential-diagram :
    ( c' : cocone-sequential-diagram A X) → ( c ＝ c') →
    htpy-cocone-sequential-diagram c c'
  htpy-eq-cocone-sequential-diagram .c refl =
    refl-htpy-cocone-sequential-diagram

  abstract
    is-torsorial-htpy-cocone-sequential-diagram :
      is-torsorial (htpy-cocone-sequential-diagram c)
    is-torsorial-htpy-cocone-sequential-diagram =
      is-torsorial-Eq-structure
        ( is-torsorial-binary-htpy (map-cocone-sequential-diagram c))
        ( ( map-cocone-sequential-diagram c) ,
          ( ev-pair refl-htpy))
        ( is-torsorial-binary-htpy
          ( λ n → coherence-cocone-sequential-diagram c n ∙h refl-htpy))

    is-equiv-htpy-eq-cocone-sequential-diagram :
      ( c' : cocone-sequential-diagram A X) →
      is-equiv (htpy-eq-cocone-sequential-diagram c')
    is-equiv-htpy-eq-cocone-sequential-diagram =
      fundamental-theorem-id
        ( is-torsorial-htpy-cocone-sequential-diagram)
        ( htpy-eq-cocone-sequential-diagram)

  extensionality-cocone-sequential-diagram :
    ( c' : cocone-sequential-diagram A X) →
    ( c ＝ c') ≃ htpy-cocone-sequential-diagram c c'
  pr1 (extensionality-cocone-sequential-diagram c') =
    htpy-eq-cocone-sequential-diagram c'
  pr2 (extensionality-cocone-sequential-diagram c') =
    is-equiv-htpy-eq-cocone-sequential-diagram c'

  eq-htpy-cocone-sequential-diagram :
    ( c' : cocone-sequential-diagram A X) →
    htpy-cocone-sequential-diagram c c' →
    c ＝ c'
  eq-htpy-cocone-sequential-diagram c' =
    map-inv-equiv (extensionality-cocone-sequential-diagram c')
```

### Postcomposing a cocone under a sequential diagram by identity is the identity

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  ( c : cocone-sequential-diagram A X)
  where

  htpy-cocone-map-id-sequential-diagram :
    htpy-cocone-sequential-diagram (cocone-map-sequential-diagram c id) c
  pr1 htpy-cocone-map-id-sequential-diagram n =
    refl-htpy
  pr2 htpy-cocone-map-id-sequential-diagram n =
    ( right-unit-htpy) ∙h
    ( left-unit-law-left-whisker-comp
      ( coherence-cocone-sequential-diagram c n))

  cocone-map-id-sequential-diagram : cocone-map-sequential-diagram c id ＝ c
  cocone-map-id-sequential-diagram =
    eq-htpy-cocone-sequential-diagram A _ _
      ( htpy-cocone-map-id-sequential-diagram)
```

### Postcomposing cocones under a sequential colimit distributes over function composition

In other words, extending a cocone `c` with vertex `X` by the map
`k ∘ h : X → Z` results in the same cocone as first extending by `h` and then by
`k`.

```agda
module _
  { l1 l2 l3 l4 : Level} (A : sequential-diagram l1)
  { X : UU l2} {Y : UU l3} {Z : UU l4}
  ( c : cocone-sequential-diagram A X)
  where

  htpy-cocone-map-comp-sequential-diagram :
    ( h : X → Y) (k : Y → Z) →
    htpy-cocone-sequential-diagram
      ( cocone-map-sequential-diagram c (k ∘ h))
      ( cocone-map-sequential-diagram (cocone-map-sequential-diagram c h) k)
  pr1 (htpy-cocone-map-comp-sequential-diagram h k) n =
    refl-htpy
  pr2 (htpy-cocone-map-comp-sequential-diagram h k) n =
    ( right-unit-htpy) ∙h
    ( inv-preserves-comp-left-whisker-comp k h
      ( coherence-cocone-sequential-diagram c n))

  cocone-map-comp-sequential-diagram :
    ( h : X → Y) (k : Y → Z) →
    cocone-map-sequential-diagram c (k ∘ h) ＝
    cocone-map-sequential-diagram (cocone-map-sequential-diagram c h) k
  cocone-map-comp-sequential-diagram h k =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram c (k ∘ h))
      ( cocone-map-sequential-diagram (cocone-map-sequential-diagram c h) k)
      ( htpy-cocone-map-comp-sequential-diagram h k)
```

## References

{{#bibliography}} {{#reference SvDR20}}
