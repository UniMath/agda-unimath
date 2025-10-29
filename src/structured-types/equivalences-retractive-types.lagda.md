# Equivalences of retractive types

```agda
module structured-types.equivalences-retractive-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
open import foundation-core.contractible-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.propositions

open import structured-types.morphisms-retractive-types
open import structured-types.retractive-types
```

</details>

## Idea

An
{{#concept "equivalence" Disambiguation="of retractive types" Agda=equiv-Retractive-Type}}
between two [retractive types](structured-types.retractive-types.md) `A` and `B`
under `X` is a
[morphism of retractive types](structured-types.morphisms-retractive-types.md)
whose underlying map is an [equivalence](foundation-core.equivalences.md) of
types. I.e., it is an equivalence `f : A ≃ B` such that the following
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

### The predicate on a morphism of retractive types under `X` of being an equivalence

```agda
module _
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X)
  (f : hom-Retractive-Type A B)
  where

  is-equiv-hom-Retractive-Type : UU (l1 ⊔ l2)
  is-equiv-hom-Retractive-Type =
    is-equiv (map-type-hom-Retractive-Type A B f)

  is-prop-is-equiv-hom-Retractive-Type : is-prop is-equiv-hom-Retractive-Type
  is-prop-is-equiv-hom-Retractive-Type =
    is-property-is-equiv (map-type-hom-Retractive-Type A B f)

  is-equiv-prop-hom-Retractive-Type : Prop (l1 ⊔ l2)
  is-equiv-prop-hom-Retractive-Type =
    is-equiv-Prop (map-type-hom-Retractive-Type A B f)
```

### The type of equivalences between two retractive types under `X`

```agda
equiv-Retractive-Type :
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X) →
  UU (l ⊔ l1 ⊔ l2)
equiv-Retractive-Type A B =
  Σ (hom-Retractive-Type A B) (is-equiv-hom-Retractive-Type A B)

module _
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X)
  (e : equiv-Retractive-Type A B)
  where

  hom-equiv-Retractive-Type : hom-Retractive-Type A B
  hom-equiv-Retractive-Type = pr1 e

  is-equiv-equiv-Retractive-Type :
    is-equiv-hom-Retractive-Type A B hom-equiv-Retractive-Type
  is-equiv-equiv-Retractive-Type = pr2 e

  map-type-equiv-Retractive-Type :
    type-Retractive-Type A → type-Retractive-Type B
  map-type-equiv-Retractive-Type =
    map-type-hom-Retractive-Type A B hom-equiv-Retractive-Type

  coh-inclusion-equiv-Retractive-Type :
    coherence-triangle-maps'
      ( inclusion-Retractive-Type B)
      ( map-type-equiv-Retractive-Type)
      ( inclusion-Retractive-Type A)
  coh-inclusion-equiv-Retractive-Type =
    coh-inclusion-hom-Retractive-Type A B hom-equiv-Retractive-Type

  coh-retraction-equiv-Retractive-Type :
    coherence-triangle-maps'
      ( map-retraction-Retractive-Type A)
      ( map-retraction-Retractive-Type B)
      ( map-type-equiv-Retractive-Type)
  coh-retraction-equiv-Retractive-Type =
    coh-retraction-hom-Retractive-Type A B hom-equiv-Retractive-Type

  coh-coh-equiv-Retractive-Type :
    coherence-of-coherence-hom-Retractive-Type A B
      ( map-type-equiv-Retractive-Type)
      ( coh-inclusion-equiv-Retractive-Type)
      ( coh-retraction-equiv-Retractive-Type)
  coh-coh-equiv-Retractive-Type =
    coh-coh-hom-Retractive-Type A B hom-equiv-Retractive-Type
```

### Alternative definition of the type of equivalences between two retractive types under `X`

```agda
equiv-Retractive-Type' :
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X) →
  UU (l ⊔ l1 ⊔ l2)
equiv-Retractive-Type' A B =
  Σ (type-Retractive-Type A ≃ type-Retractive-Type B)
    ( λ e → coherence-hom-Retractive-Type A B (map-equiv e))

module _
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X)
  (e : equiv-Retractive-Type' A B)
  where

  equiv-type-equiv-Retractive-Type' :
    type-Retractive-Type A ≃ type-Retractive-Type B
  equiv-type-equiv-Retractive-Type' = pr1 e

  map-type-equiv-Retractive-Type' :
    type-Retractive-Type A → type-Retractive-Type B
  map-type-equiv-Retractive-Type' = map-equiv equiv-type-equiv-Retractive-Type'

  coh-equiv-Retractive-Type' :
    coherence-hom-Retractive-Type A B map-type-equiv-Retractive-Type'
  coh-equiv-Retractive-Type' = pr2 e

  hom-equiv-Retractive-Type' : hom-Retractive-Type A B
  hom-equiv-Retractive-Type' =
    ( map-type-equiv-Retractive-Type' , coh-equiv-Retractive-Type')

  is-equiv-equiv-Retractive-Type' :
    is-equiv-hom-Retractive-Type A B hom-equiv-Retractive-Type'
  is-equiv-equiv-Retractive-Type' =
    is-equiv-map-equiv equiv-type-equiv-Retractive-Type'

  coh-inclusion-equiv-Retractive-Type' :
    coherence-triangle-maps'
      ( inclusion-Retractive-Type B)
      ( map-type-equiv-Retractive-Type')
      ( inclusion-Retractive-Type A)
  coh-inclusion-equiv-Retractive-Type' =
    coh-inclusion-hom-Retractive-Type A B hom-equiv-Retractive-Type'

  coh-retraction-equiv-Retractive-Type' :
    coherence-triangle-maps'
      ( map-retraction-Retractive-Type A)
      ( map-retraction-Retractive-Type B)
      ( map-type-equiv-Retractive-Type')
  coh-retraction-equiv-Retractive-Type' =
    coh-retraction-hom-Retractive-Type A B hom-equiv-Retractive-Type'

  coh-coh-equiv-Retractive-Type' :
    coherence-of-coherence-hom-Retractive-Type A B
      ( map-type-equiv-Retractive-Type')
      ( coh-inclusion-equiv-Retractive-Type')
      ( coh-retraction-equiv-Retractive-Type')
  coh-coh-equiv-Retractive-Type' =
    coh-coh-hom-Retractive-Type A B hom-equiv-Retractive-Type'

module _
  {l l1 l2 : Level} {X : UU l}
  (A : Retractive-Type l1 X) (B : Retractive-Type l2 X)
  where

  compute-equiv-Retractive-Type :
    equiv-Retractive-Type A B ≃ equiv-Retractive-Type' A B
  compute-equiv-Retractive-Type = equiv-right-swap-Σ
```

### The identity equivalence

```agda
id-equiv-Retractive-Type :
  {l1 l2 : Level} {X : UU l1} (A : Retractive-Type l2 X) →
  equiv-Retractive-Type A A
id-equiv-Retractive-Type A = (id-hom-Retractive-Type A , is-equiv-id)

id-equiv-Retractive-Type' :
  {l1 l2 : Level} {X : UU l1} (A : Retractive-Type l2 X) →
  equiv-Retractive-Type' A A
id-equiv-Retractive-Type' A = (id-equiv , refl-htpy , refl-htpy , refl-htpy)
```

## Properties

### Equivalences of retractive types characterize their equality

```agda
module _
  {l1 l2 : Level} {X : UU l1}
  where

  equiv-eq-Retractive-Type' :
    (A B : Retractive-Type l2 X) → A ＝ B → equiv-Retractive-Type' A B
  equiv-eq-Retractive-Type' A .A refl = id-equiv-Retractive-Type' A

  abstract
    is-torsorial-equiv-Retractive-Type' :
      (A : Retractive-Type l2 X) → is-torsorial (equiv-Retractive-Type' A)
    is-torsorial-equiv-Retractive-Type' A =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (type-Retractive-Type A))
        ( type-Retractive-Type A , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (inclusion-Retractive-Type A))
          ( inclusion-Retractive-Type A , refl-htpy)
          ( is-torsorial-Eq-structure
            ( is-torsorial-htpy' (map-retraction-Retractive-Type A))
            ( map-retraction-Retractive-Type A , refl-htpy)
            ( is-torsorial-htpy' (is-retract-Retractive-Type A))))

  abstract
    is-equiv-equiv-eq-Retractive-Type' :
      (A B : Retractive-Type l2 X) → is-equiv (equiv-eq-Retractive-Type' A B)
    is-equiv-equiv-eq-Retractive-Type' A =
      fundamental-theorem-id
        ( is-torsorial-equiv-Retractive-Type' A)
        ( equiv-eq-Retractive-Type' A)

  extensionality-Retractive-Type' :
    (A B : Retractive-Type l2 X) → (A ＝ B) ≃ equiv-Retractive-Type' A B
  extensionality-Retractive-Type' A B =
    ( equiv-eq-Retractive-Type' A B , is-equiv-equiv-eq-Retractive-Type' A B)

  eq-equiv-Retractive-Type' :
    (A B : Retractive-Type l2 X) → equiv-Retractive-Type' A B → A ＝ B
  eq-equiv-Retractive-Type' A B =
    map-inv-equiv (extensionality-Retractive-Type' A B)

module _
  {l1 l2 : Level} {X : UU l1}
  where

  equiv-eq-Retractive-Type :
    (A B : Retractive-Type l2 X) → A ＝ B → equiv-Retractive-Type A B
  equiv-eq-Retractive-Type A .A refl = id-equiv-Retractive-Type A

  abstract
    is-torsorial-equiv-Retractive-Type :
      (A : Retractive-Type l2 X) → is-torsorial (equiv-Retractive-Type A)
    is-torsorial-equiv-Retractive-Type A =
      is-contr-equiv _
        ( equiv-tot (compute-equiv-Retractive-Type A))
        ( is-torsorial-equiv-Retractive-Type' A)

  abstract
    is-equiv-equiv-eq-Retractive-Type :
      (A B : Retractive-Type l2 X) → is-equiv (equiv-eq-Retractive-Type A B)
    is-equiv-equiv-eq-Retractive-Type A =
      fundamental-theorem-id
        ( is-torsorial-equiv-Retractive-Type A)
        ( equiv-eq-Retractive-Type A)

  extensionality-Retractive-Type :
    (A B : Retractive-Type l2 X) → (A ＝ B) ≃ equiv-Retractive-Type A B
  extensionality-Retractive-Type A B =
    ( equiv-eq-Retractive-Type A B , is-equiv-equiv-eq-Retractive-Type A B)

  eq-equiv-Retractive-Type :
    (A B : Retractive-Type l2 X) → equiv-Retractive-Type A B → A ＝ B
  eq-equiv-Retractive-Type A B =
    map-inv-equiv (extensionality-Retractive-Type A B)
```
