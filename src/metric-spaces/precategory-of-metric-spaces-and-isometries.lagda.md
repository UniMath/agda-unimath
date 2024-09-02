# The precategory of metric spaces and isometries

```agda
module metric-spaces.precategory-of-metric-spaces-and-isometries where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-precategories
open import category-theory.precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import metric-spaces.equality-of-metric-spaces
open import metric-spaces.functions-metric-spaces
open import metric-spaces.isometry-metric-spaces
open import metric-spaces.metric-spaces
```

</details>

## Idea

The [isometries](metric-spaces.isometry-metric-spaces.md) form a
[precategory](category-theory.precategories.md).

## Definitions

```agda
module _
  {l1 l2 : Level}
  where

  precategory-isometry-Metric-Space :
    Precategory (lsuc l1 ⊔ lsuc l2) (l1 ⊔ l2)
  precategory-isometry-Metric-Space =
    make-Precategory
      ( Metric-Space l1 l2)
      ( set-isometry-Metric-Space)
      ( λ {A B C} → comp-isometry-Metric-Space A B C)
      ( isometry-id-Metric-Space)
      ( λ {A B C D} h g f →
        eq-htpy-map-isometry-Metric-Space
          ( A)
          ( D)
          ( comp-isometry-Metric-Space A B D
            ( comp-isometry-Metric-Space B C D h g)
            ( f))
          ( comp-isometry-Metric-Space A C D
            ( h)
            ( comp-isometry-Metric-Space A B C g f))
          ( λ x → refl))
      ( λ {A B} f →
        eq-htpy-map-isometry-Metric-Space A B
          ( comp-isometry-Metric-Space A B B
            ( isometry-id-Metric-Space B)
            ( f))
          ( f)
          ( λ x → refl))
      ( λ {A B} f →
        eq-htpy-map-isometry-Metric-Space A B
          ( comp-isometry-Metric-Space A A B
            ( f)
            ( isometry-id-Metric-Space A))
          ( f)
          ( λ x → refl))
```

## Properties

### Isomorphisms in the precategory of metric spaces and isometries are equivalences

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : isometry-Metric-Space A B)
  where

  is-equiv-is-iso-precatory-isometry-Metric-Space :
    is-iso-Precategory precategory-isometry-Metric-Space {A} {B} f →
    is-equiv (map-isometry-Metric-Space A B f)
  is-equiv-is-iso-precatory-isometry-Metric-Space =
    rec-Σ
      ( λ g H →
        is-equiv-is-invertible
          ( map-isometry-Metric-Space B A g)
          ( htpy-eq (ap (map-isometry-Metric-Space B B) (pr1 H)))
          ( htpy-eq (ap (map-isometry-Metric-Space A A) (pr2 H))))
```

### Isometric equivalences are isomorphisms in the precategory of metric spaces and isometries

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  (f : isometry-Metric-Space A B)
  (E : is-equiv (map-isometry-Metric-Space A B f))
  where

  is-iso-precategory-is-equiv-isometry-Metric-Space :
    is-iso-Precategory precategory-isometry-Metric-Space {A} {B} f
  is-iso-precategory-is-equiv-isometry-Metric-Space =
    ( isometry-inverse) ,
    ( ( eq-htpy-map-isometry-Metric-Space
        ( B)
        ( B)
        ( comp-isometry-Metric-Space B A B f isometry-inverse)
        ( isometry-id-Metric-Space B)
        ( is-section-map-inv-is-equiv E)) ,
      ( eq-htpy-map-isometry-Metric-Space
        ( A)
        ( A)
        ( comp-isometry-Metric-Space A B A isometry-inverse f))
        ( isometry-id-Metric-Space A)
        ( is-retraction-map-inv-is-equiv E))
    where

    isometry-inverse : isometry-Metric-Space B A
    isometry-inverse =
      isometry-inv-is-equiv-is-isometry-Metric-Space
        ( A)
        ( B)
        ( map-isometry-Metric-Space A B f)
        ( E)
        ( is-isometry-map-isometry-Metric-Space A B f)
```

### Isomorphic types in the precategory of metric spaces are isometrically equivalent

```agda
module _
  {l1 l2 : Level} (A B : Metric-Space l1 l2)
  where

  equiv-iso-isometric-is-equiv-Metric-Space :
    iso-Precategory precategory-isometry-Metric-Space A B ≃
    isometric-is-equiv-Metric-Space A B
  equiv-iso-isometric-is-equiv-Metric-Space =
    equiv-tot (λ f → commutative-product) ∘e
    associative-Σ
      ( function-carrier-type-Metric-Space A B)
      ( is-isometry-Metric-Space A B)
      ( is-equiv ∘ map-isometry-Metric-Space A B) ∘e
    equiv-tot
      ( λ f →
        equiv-iff
          ( is-iso-prop-Precategory
            ( precategory-isometry-Metric-Space)
            { A}
            { B}
            ( f))
          ( is-equiv-Prop
            ( map-isometry-Metric-Space A B f))
          ( is-equiv-is-iso-precatory-isometry-Metric-Space A B f)
          ( is-iso-precategory-is-equiv-isometry-Metric-Space A B f))
```

### Isomorphism in the precategory of metric spaces and isometries is torsorial

```agda
module _
  {l1 l2 : Level} (A : Metric-Space l1 l2)
  where

  is-torsorial-iso-precategory-isometry-Metric-Space :
    is-torsorial (iso-Precategory precategory-isometry-Metric-Space A)
  is-torsorial-iso-precategory-isometry-Metric-Space =
    is-contr-equiv
      ( Σ (Metric-Space l1 l2) (isometric-is-equiv-Metric-Space A))
      ( equiv-tot (equiv-iso-isometric-is-equiv-Metric-Space A))
      ( is-torsorial-isometric-is-equiv-Metric-Space A)
```