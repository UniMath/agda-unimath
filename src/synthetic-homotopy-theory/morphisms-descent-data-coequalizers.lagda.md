# Morphisms of descent data for coequalizers

```agda
module synthetic-homotopy-theory.morphisms-descent-data-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.descent-data-coequalizers
```

</details>

## Idea

A
{{#concept "morphism of descent data" Disambiguation="coequalizers" Agda=hom-descent-data-coequalizer}}
between `(PB, PA)` and `(QB, QA)` is a fiberwise map `h : (b : B) → PB b → QB b`
equipped with a family of homotopies

```text
             h (f a)
   PB (f a) ---------> QB (f a)
       |                   |
  PA a |                   | QA a
       |                   |
       ∨                   ∨
   PB (g a) ---------> QB (g a) .
             h (g a)
```

## Definitions

### Morphisms of descent data for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  where

  hom-descent-data-coequalizer : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-descent-data-coequalizer =
    Σ ( (b : codomain-double-arrow F) →
        family-descent-data-coequalizer P b →
        family-descent-data-coequalizer Q b)
      ( λ h →
        ( a : domain-double-arrow F) →
        coherence-square-maps
          ( h (left-map-double-arrow F a))
          ( map-family-descent-data-coequalizer P a)
          ( map-family-descent-data-coequalizer Q a)
          ( h (right-map-double-arrow F a)))

  module _
    (h : hom-descent-data-coequalizer)
    where

    map-hom-descent-data-coequalizer :
      (a : codomain-double-arrow F) →
      family-descent-data-coequalizer P a →
      family-descent-data-coequalizer Q a
    map-hom-descent-data-coequalizer = pr1 h

    coherence-hom-descent-data-coequalizer :
      (a : domain-double-arrow F) →
      coherence-square-maps
        ( map-hom-descent-data-coequalizer (left-map-double-arrow F a))
        ( map-family-descent-data-coequalizer P a)
        ( map-family-descent-data-coequalizer Q a)
        ( map-hom-descent-data-coequalizer (right-map-double-arrow F a))
    coherence-hom-descent-data-coequalizer = pr2 h
```

### The identity morphism of descent data for coequalizers

```agda
module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  where

  id-hom-descent-data-coequalizer : hom-descent-data-coequalizer P P
  pr1 id-hom-descent-data-coequalizer a = id
  pr2 id-hom-descent-data-coequalizer s = refl-htpy
```

### Composition of morphisms of descent dat afor coequalizers

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  (R : descent-data-coequalizer F l5)
  (g : hom-descent-data-coequalizer Q R)
  (f : hom-descent-data-coequalizer P Q)
  where

  comp-hom-descent-data-coequalizer : hom-descent-data-coequalizer P R
  pr1 comp-hom-descent-data-coequalizer b =
    map-hom-descent-data-coequalizer Q R g b ∘
    map-hom-descent-data-coequalizer P Q f b
  pr2 comp-hom-descent-data-coequalizer a =
    pasting-horizontal-coherence-square-maps
      ( map-hom-descent-data-coequalizer P Q f (left-map-double-arrow F a))
      ( map-hom-descent-data-coequalizer Q R g (left-map-double-arrow F a))
      ( map-family-descent-data-coequalizer P a)
      ( map-family-descent-data-coequalizer Q a)
      ( map-family-descent-data-coequalizer R a)
      ( map-hom-descent-data-coequalizer P Q f (right-map-double-arrow F a))
      ( map-hom-descent-data-coequalizer Q R g (right-map-double-arrow F a))
      ( coherence-hom-descent-data-coequalizer P Q f a)
      ( coherence-hom-descent-data-coequalizer Q R g a)
```

### Homotopies between morphisms of descent data for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  (f g : hom-descent-data-coequalizer P Q)
  where

  htpy-hom-descent-data-coequalizer : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-descent-data-coequalizer =
    Σ ( (b : codomain-double-arrow F) →
        map-hom-descent-data-coequalizer P Q f b ~
        map-hom-descent-data-coequalizer P Q g b)
      ( λ H →
        (a : domain-double-arrow F) →
        ( ( coherence-hom-descent-data-coequalizer P Q f a) ∙h
          ( ( map-family-descent-data-coequalizer Q a) ·l
            ( H (left-map-double-arrow F a)))) ~
        ( ( H (right-map-double-arrow F a)) ·r
          ( map-family-descent-data-coequalizer P a)) ∙h
        ( coherence-hom-descent-data-coequalizer P Q g a))
```

### The reflexive homotopy between morphisms of descent data for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  (f : hom-descent-data-coequalizer P Q)
  where

  refl-htpy-hom-descent-data-coequalizer :
    htpy-hom-descent-data-coequalizer P Q f f
  pr1 refl-htpy-hom-descent-data-coequalizer b = refl-htpy
  pr2 refl-htpy-hom-descent-data-coequalizer a = right-unit-htpy
```

## Properties

### Characterizing the identity type of morphisms of descent data for coequalizers

```agda
module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  (P : descent-data-coequalizer F l3)
  (Q : descent-data-coequalizer F l4)
  (f : hom-descent-data-coequalizer P Q)
  where

  htpy-eq-hom-descent-data-coequalizer :
    (g : hom-descent-data-coequalizer P Q) →
    (f ＝ g) → htpy-hom-descent-data-coequalizer P Q f g
  htpy-eq-hom-descent-data-coequalizer .f refl =
    refl-htpy-hom-descent-data-coequalizer P Q f

  abstract
    is-torsorial-htpy-hom-descent-data-coequalizer :
      is-torsorial (htpy-hom-descent-data-coequalizer P Q f)
    is-torsorial-htpy-hom-descent-data-coequalizer =
      is-torsorial-Eq-structure
        ( is-torsorial-Eq-Π
          ( λ b →
            is-torsorial-htpy (map-hom-descent-data-coequalizer P Q f b)))
        ( map-hom-descent-data-coequalizer P Q f , λ b → refl-htpy)
        ( is-torsorial-Eq-Π
          ( λ a →
            is-torsorial-htpy
              ( coherence-hom-descent-data-coequalizer P Q f a ∙h refl-htpy)))

  is-equiv-htpy-eq-hom-descent-data-coequalizer :
    (g : hom-descent-data-coequalizer P Q) →
    is-equiv (htpy-eq-hom-descent-data-coequalizer g)
  is-equiv-htpy-eq-hom-descent-data-coequalizer =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-descent-data-coequalizer)
      ( htpy-eq-hom-descent-data-coequalizer)

  extensionality-hom-descent-data-coequalizer :
    (g : hom-descent-data-coequalizer P Q) →
    (f ＝ g) ≃ htpy-hom-descent-data-coequalizer P Q f g
  pr1 (extensionality-hom-descent-data-coequalizer g) =
    htpy-eq-hom-descent-data-coequalizer g
  pr2 (extensionality-hom-descent-data-coequalizer g) =
    is-equiv-htpy-eq-hom-descent-data-coequalizer g

  eq-htpy-hom-descent-data-coequalizer :
    (g : hom-descent-data-coequalizer P Q) →
    htpy-hom-descent-data-coequalizer P Q f g → f ＝ g
  eq-htpy-hom-descent-data-coequalizer g =
    map-inv-equiv (extensionality-hom-descent-data-coequalizer g)
```
