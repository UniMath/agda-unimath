# Morphisms of retractive types

```agda
module structured-types.morphisms-retractive-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-tetrahedra-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import foundation-core.homotopies

open import structured-types.retractive-types
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of retractive types" Agda=hom-Retractive-Type}}
between two [retractive types](structured-types.retractive-types.md) `A` and `B`
under `X` is a map of the underlying types `f : A → B` such that the following
[tetrahedron](foundation.commuting-tetrahedra-of-maps.md) commutes

```text
    X ----------> B
    | \\       ∧  |
    |   \\   /    |
    |      /      |
    |   f/  \\    |
    ∨  /      \\  ∨
    A ----------> X.
```

## Definition

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X)
  where

  coherence-of-coherence-hom-Retractive-Type :
    (f : type-Retractive-Type A → type-Retractive-Type B) →
    coherence-triangle-maps'
      ( inclusion-Retractive-Type B)
      ( f)
      ( inclusion-Retractive-Type A) →
    coherence-triangle-maps'
      ( map-retraction-Retractive-Type A)
      ( map-retraction-Retractive-Type B)
      ( f) →
    UU l
  coherence-of-coherence-hom-Retractive-Type f H K =
    coherence-reverse-tetrahedron-maps
      ( inclusion-Retractive-Type B)
      ( inclusion-Retractive-Type A)
      ( map-retraction-Retractive-Type B)
      ( map-retraction-Retractive-Type A)
      ( f)
      ( id' X)
      ( H)
      ( K)
      ( is-retract-Retractive-Type B)
      ( is-retract-Retractive-Type A)

  coherence-hom-Retractive-Type :
    (f : type-Retractive-Type A → type-Retractive-Type B) → UU (l ⊔ l1 ⊔ l2)
  coherence-hom-Retractive-Type f =
    Σ ( coherence-triangle-maps'
        ( inclusion-Retractive-Type B)
        ( f)
        ( inclusion-Retractive-Type A))
      ( λ H →
        Σ ( coherence-triangle-maps'
            ( map-retraction-Retractive-Type A)
            ( map-retraction-Retractive-Type B)
            ( f))
          ( λ K → coherence-of-coherence-hom-Retractive-Type f H K))

  hom-Retractive-Type : UU (l ⊔ l1 ⊔ l2)
  hom-Retractive-Type =
    Σ ( type-Retractive-Type A → type-Retractive-Type B)
      ( coherence-hom-Retractive-Type)

module _
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X)
  (f : hom-Retractive-Type A B)
  where

  map-type-hom-Retractive-Type :
    type-Retractive-Type A → type-Retractive-Type B
  map-type-hom-Retractive-Type = pr1 f

  coh-hom-Retractive-Type :
    coherence-hom-Retractive-Type A B map-type-hom-Retractive-Type
  coh-hom-Retractive-Type = pr2 f

  coh-inclusion-hom-Retractive-Type :
    coherence-triangle-maps'
      ( inclusion-Retractive-Type B)
      ( map-type-hom-Retractive-Type)
      ( inclusion-Retractive-Type A)
  coh-inclusion-hom-Retractive-Type = pr1 coh-hom-Retractive-Type

  coh-retraction-hom-Retractive-Type :
    coherence-triangle-maps'
      ( map-retraction-Retractive-Type A)
      ( map-retraction-Retractive-Type B)
      ( map-type-hom-Retractive-Type)
  coh-retraction-hom-Retractive-Type = pr1 (pr2 coh-hom-Retractive-Type)

  coh-coh-hom-Retractive-Type :
    coherence-of-coherence-hom-Retractive-Type A B
      ( map-type-hom-Retractive-Type)
      ( coh-inclusion-hom-Retractive-Type)
      ( coh-retraction-hom-Retractive-Type)
  coh-coh-hom-Retractive-Type = pr2 (pr2 coh-hom-Retractive-Type)
```

### The identity morphism

```agda
id-hom-Retractive-Type :
  {l1 l2 : Level} {X : UU l1}
  (A : Retractive-Type l2 X) →
  hom-Retractive-Type A A
id-hom-Retractive-Type A =
  ( id , refl-htpy , refl-htpy , refl-htpy)
```
