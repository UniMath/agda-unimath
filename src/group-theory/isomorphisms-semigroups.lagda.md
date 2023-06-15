# Isomorphisms of semigroups

```agda
module group-theory.isomorphisms-semigroups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-extensionality

open import group-theory.equivalences-semigroups
open import group-theory.homomorphisms-semigroups
open import group-theory.precategory-of-semigroups
open import group-theory.semigroups
```

</details>

## Idea

Isomorphisms of semigroups are homomorphisms that have a two-sided inverse.

## Definition

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  is-iso-hom-Semigroup : (f : type-hom-Semigroup G H) → UU (l1 ⊔ l2)
  is-iso-hom-Semigroup f =
    is-iso-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  inv-is-iso-hom-Semigroup :
    (f : type-hom-Semigroup G H) →
    is-iso-hom-Semigroup f → type-hom-Semigroup H G
  inv-is-iso-hom-Semigroup f = pr1

  type-iso-Semigroup : UU (l1 ⊔ l2)
  type-iso-Semigroup = iso-Large-Precategory Semigroup-Large-Precategory G H

  hom-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup G H
  hom-iso-Semigroup = hom-iso-Large-Precategory Semigroup-Large-Precategory G H

  is-iso-hom-iso-Semigroup :
    (f : type-iso-Semigroup) → is-iso-hom-Semigroup (hom-iso-Semigroup f)
  is-iso-hom-iso-Semigroup =
    is-iso-hom-iso-Large-Precategory Semigroup-Large-Precategory G H

  hom-inv-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup H G
  hom-inv-iso-Semigroup =
    hom-inv-iso-Large-Precategory Semigroup-Large-Precategory G H

  is-section-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    Id
      ( comp-hom-Semigroup H G H
        ( hom-iso-Semigroup f)
        ( hom-inv-iso-Semigroup f))
      ( id-hom-Semigroup H)
  is-section-hom-inv-iso-Semigroup =
    is-section-hom-inv-iso-Large-Precategory Semigroup-Large-Precategory G H

  is-retraction-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    Id
      ( comp-hom-Semigroup G H G
        ( hom-inv-iso-Semigroup f)
        ( hom-iso-Semigroup f))
      ( id-hom-Semigroup G)
  is-retraction-hom-inv-iso-Semigroup =
    is-retraction-hom-inv-iso-Large-Precategory Semigroup-Large-Precategory G H
```

## Properties

### Being an isomorphism is a property

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-prop-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) → is-prop (is-iso-hom-Semigroup G H f)
    is-prop-is-iso-hom-Semigroup =
      is-prop-is-iso-Large-Precategory Semigroup-Large-Precategory G H
```

### The inverse of an equivalence of semigroups preserves the binary operation

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : type-hom-Semigroup G H)
      ( is-equiv-f : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv is-equiv-f)
    preserves-mul-map-inv-is-equiv-Semigroup (pair f μ-f) is-equiv-f x y =
      map-inv-is-equiv
        ( is-emb-is-equiv is-equiv-f
          ( map-inv-is-equiv is-equiv-f (mul-Semigroup H x y))
          ( mul-Semigroup G
            ( map-inv-is-equiv is-equiv-f x)
            ( map-inv-is-equiv is-equiv-f y)))
        ( ( ( is-section-map-inv-is-equiv is-equiv-f (mul-Semigroup H x y)) ∙
            ( ( ap
                ( λ t → mul-Semigroup H t y)
                ( inv (is-section-map-inv-is-equiv is-equiv-f x))) ∙
              ( ap
                ( mul-Semigroup H (f (map-inv-is-equiv is-equiv-f x)))
                ( inv (is-section-map-inv-is-equiv is-equiv-f y))))) ∙
          ( inv
            ( μ-f
              ( map-inv-is-equiv is-equiv-f x)
              ( map-inv-is-equiv is-equiv-f y))))
```

### A homomorphism of semigroups is an equivalence of semigroups if and only if it is an isomorphism

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    is-iso-is-equiv-hom-Semigroup :
      (f : type-hom-Semigroup G H) →
      is-equiv-hom-Semigroup G H f → is-iso-hom-Semigroup G H f
    pr1 (pr1 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      map-inv-is-equiv is-equiv-f
    pr2 (pr1 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      preserves-mul-map-inv-is-equiv-Semigroup G H (pair f μ-f) is-equiv-f
    pr1 (pr2 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      eq-htpy-hom-Semigroup H H (is-section-map-inv-is-equiv is-equiv-f)
    pr2 (pr2 (is-iso-is-equiv-hom-Semigroup (pair f μ-f) is-equiv-f)) =
      eq-htpy-hom-Semigroup G G (is-retraction-map-inv-is-equiv is-equiv-f)

  abstract
    is-equiv-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) →
      is-iso-hom-Semigroup G H f → is-equiv-hom-Semigroup G H f
    is-equiv-is-iso-hom-Semigroup
      ( pair f μ-f)
      ( pair (pair g μ-g) (pair is-section is-retraction)) =
      is-equiv-has-inverse g
        ( htpy-eq (ap pr1 is-section))
        ( htpy-eq (ap pr1 is-retraction))

  equiv-iso-equiv-Semigroup : equiv-Semigroup G H ≃ type-iso-Semigroup G H
  equiv-iso-equiv-Semigroup =
    ( equiv-type-subtype
      ( λ f → is-property-is-equiv (map-hom-Semigroup G H f))
      ( is-prop-is-iso-hom-Semigroup G H)
      ( is-iso-is-equiv-hom-Semigroup)
      ( is-equiv-is-iso-hom-Semigroup)) ∘e
    ( equiv-right-swap-Σ)
```

### Two semigroups are equal if and only if they are isomorphic

```agda
module _
  {l : Level} (G : Semigroup l)
  where

  is-contr-total-iso-Semigroup :
    is-contr (Σ (Semigroup l) (type-iso-Semigroup G))
  is-contr-total-iso-Semigroup =
    is-contr-equiv'
      ( Σ (Semigroup l) (equiv-Semigroup G))
      ( equiv-tot (equiv-iso-equiv-Semigroup G))
      ( is-contr-total-equiv-Semigroup G)

  id-iso-Semigroup : type-iso-Semigroup G G
  id-iso-Semigroup =
    id-iso-Large-Precategory Semigroup-Large-Precategory {X = G}

  iso-eq-Semigroup : (H : Semigroup l) → Id G H → type-iso-Semigroup G H
  iso-eq-Semigroup = iso-eq-Large-Precategory Semigroup-Large-Precategory G
```
