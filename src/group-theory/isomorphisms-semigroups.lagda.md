# Isomorphisms of semigroups

```agda
module group-theory.isomorphisms-semigroups where
```

<details><summary>Imports</summary>

```agda
open import category-theory.isomorphisms-in-large-precategories

open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
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

### The predicate of being an isomorphism of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  (f : type-hom-Semigroup G H)
  where

  is-iso-hom-Semigroup : UU (l1 ⊔ l2)
  is-iso-hom-Semigroup =
    is-iso-hom-Large-Precategory Semigroup-Large-Precategory {X = G} {Y = H} f

  hom-inv-is-iso-hom-Semigroup :
    is-iso-hom-Semigroup → type-hom-Semigroup H G
  hom-inv-is-iso-hom-Semigroup =
    hom-inv-is-iso-hom-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  map-inv-is-iso-hom-Semigroup :
    is-iso-hom-Semigroup → type-Semigroup H → type-Semigroup G
  map-inv-is-iso-hom-Semigroup U =
    map-hom-Semigroup H G (hom-inv-is-iso-hom-Semigroup U)

  is-section-hom-inv-is-iso-hom-Semigroup :
    (U : is-iso-hom-Semigroup) →
    comp-hom-Semigroup H G H f (hom-inv-is-iso-hom-Semigroup U) ＝
    id-hom-Semigroup H
  is-section-hom-inv-is-iso-hom-Semigroup =
    is-section-hom-inv-is-iso-hom-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  is-section-map-inv-is-iso-hom-Semigroup :
    (U : is-iso-hom-Semigroup) →
    ( map-hom-Semigroup G H f ∘ map-inv-is-iso-hom-Semigroup U) ~ id
  is-section-map-inv-is-iso-hom-Semigroup U =
    htpy-eq-hom-Semigroup H H
      ( comp-hom-Semigroup H G H f (hom-inv-is-iso-hom-Semigroup U))
      ( id-hom-Semigroup H)
      ( is-section-hom-inv-is-iso-hom-Semigroup U)

  is-retraction-hom-inv-is-iso-hom-Semigroup :
    (U : is-iso-hom-Semigroup) →
    comp-hom-Semigroup G H G (hom-inv-is-iso-hom-Semigroup U) f ＝
    id-hom-Semigroup G
  is-retraction-hom-inv-is-iso-hom-Semigroup =
    is-retraction-hom-inv-is-iso-hom-Large-Precategory
      ( Semigroup-Large-Precategory)
      { X = G}
      { Y = H}
      ( f)

  is-retraction-map-inv-is-iso-hom-Semigroup :
    (U : is-iso-hom-Semigroup) →
    ( map-inv-is-iso-hom-Semigroup U ∘ map-hom-Semigroup G H f) ~ id
  is-retraction-map-inv-is-iso-hom-Semigroup U =
    htpy-eq-hom-Semigroup G G
      ( comp-hom-Semigroup G H G (hom-inv-is-iso-hom-Semigroup U) f)
      ( id-hom-Semigroup G)
      ( is-retraction-hom-inv-is-iso-hom-Semigroup U)
```

### Isomorphisms of semigroups

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  type-iso-Semigroup : UU (l1 ⊔ l2)
  type-iso-Semigroup = iso-Large-Precategory Semigroup-Large-Precategory G H

  hom-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup G H
  hom-iso-Semigroup = hom-iso-Large-Precategory Semigroup-Large-Precategory G H

  map-iso-Semigroup : type-iso-Semigroup → type-Semigroup G → type-Semigroup H
  map-iso-Semigroup f = map-hom-Semigroup G H (hom-iso-Semigroup f)

  preserves-mul-iso-Semigroup :
    (f : type-iso-Semigroup) (x y : type-Semigroup G) →
    map-iso-Semigroup f (mul-Semigroup G x y) ＝
    mul-Semigroup H (map-iso-Semigroup f x) (map-iso-Semigroup f y)
  preserves-mul-iso-Semigroup f =
    preserves-mul-hom-Semigroup G H (hom-iso-Semigroup f)

  is-iso-iso-Semigroup :
    (f : type-iso-Semigroup) → is-iso-hom-Semigroup G H (hom-iso-Semigroup f)
  is-iso-iso-Semigroup =
    is-iso-iso-Large-Precategory Semigroup-Large-Precategory G H

  hom-inv-iso-Semigroup : type-iso-Semigroup → type-hom-Semigroup H G
  hom-inv-iso-Semigroup =
    hom-inv-iso-Large-Precategory Semigroup-Large-Precategory G H

  map-inv-iso-Semigroup :
    type-iso-Semigroup → type-Semigroup H → type-Semigroup G
  map-inv-iso-Semigroup f =
    map-hom-Semigroup H G (hom-inv-iso-Semigroup f)

  preserves-mul-inv-iso-Semigroup :
    (f : type-iso-Semigroup) (x y : type-Semigroup H) →
    map-inv-iso-Semigroup f (mul-Semigroup H x y) ＝
    mul-Semigroup G (map-inv-iso-Semigroup f x) (map-inv-iso-Semigroup f y)
  preserves-mul-inv-iso-Semigroup f =
    preserves-mul-hom-Semigroup H G (hom-inv-iso-Semigroup f)

  is-section-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    comp-hom-Semigroup H G H (hom-iso-Semigroup f) (hom-inv-iso-Semigroup f) ＝
    id-hom-Semigroup H
  is-section-hom-inv-iso-Semigroup =
    is-section-hom-inv-iso-Large-Precategory Semigroup-Large-Precategory G H

  is-section-map-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    (map-iso-Semigroup f ∘ map-inv-iso-Semigroup f) ~ id
  is-section-map-inv-iso-Semigroup f =
    htpy-eq-hom-Semigroup H H
      ( comp-hom-Semigroup H G H
        ( hom-iso-Semigroup f)
        ( hom-inv-iso-Semigroup f))
      ( id-hom-Semigroup H)
      ( is-section-hom-inv-iso-Semigroup f)

  is-retraction-hom-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    comp-hom-Semigroup G H G (hom-inv-iso-Semigroup f) (hom-iso-Semigroup f) ＝
    id-hom-Semigroup G
  is-retraction-hom-inv-iso-Semigroup =
    is-retraction-hom-inv-iso-Large-Precategory Semigroup-Large-Precategory G H

  is-retraction-map-inv-iso-Semigroup :
    (f : type-iso-Semigroup) →
    ( map-inv-iso-Semigroup f ∘ map-iso-Semigroup f) ~ id
  is-retraction-map-inv-iso-Semigroup f =
    htpy-eq-hom-Semigroup G G
      ( comp-hom-Semigroup G H G
        ( hom-inv-iso-Semigroup f)
        ( hom-iso-Semigroup f))
      ( id-hom-Semigroup G)
      ( is-retraction-hom-inv-iso-Semigroup f)
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
      is-prop-is-iso-hom-Large-Precategory Semigroup-Large-Precategory G H

  is-iso-prop-hom-Semigroup :
    type-hom-Semigroup G H → Prop (l1 ⊔ l2)
  is-iso-prop-hom-Semigroup =
    is-iso-prop-hom-Large-Precategory Semigroup-Large-Precategory G H
```

### The inverse of an equivalence of semigroups preserves the binary operation

```agda
module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  abstract
    preserves-mul-map-inv-is-equiv-Semigroup :
      ( f : type-hom-Semigroup G H)
      ( U : is-equiv (map-hom-Semigroup G H f)) →
      preserves-mul-Semigroup H G (map-inv-is-equiv U)
    preserves-mul-map-inv-is-equiv-Semigroup (f , μ-f) U x y =
      map-inv-is-equiv
        ( is-emb-is-equiv U
          ( map-inv-is-equiv U (mul-Semigroup H x y))
          ( mul-Semigroup G
            ( map-inv-is-equiv U x)
            ( map-inv-is-equiv U y)))
        ( ( ( is-section-map-inv-is-equiv U (mul-Semigroup H x y)) ∙
            ( ( ap
                ( λ t → mul-Semigroup H t y)
                ( inv (is-section-map-inv-is-equiv U x))) ∙
              ( ap
                ( mul-Semigroup H (f (map-inv-is-equiv U x)))
                ( inv (is-section-map-inv-is-equiv U y))))) ∙
          ( inv
            ( μ-f
              ( map-inv-is-equiv U x)
              ( map-inv-is-equiv U y))))
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
    pr1 (pr1 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      map-inv-is-equiv U
    pr2 (pr1 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      preserves-mul-map-inv-is-equiv-Semigroup G H (f , μ-f) U
    pr1 (pr2 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      eq-htpy-hom-Semigroup H H (is-section-map-inv-is-equiv U)
    pr2 (pr2 (is-iso-is-equiv-hom-Semigroup (f , μ-f) U)) =
      eq-htpy-hom-Semigroup G G (is-retraction-map-inv-is-equiv U)

  abstract
    is-equiv-is-iso-hom-Semigroup :
      (f : type-hom-Semigroup G H) →
      is-iso-hom-Semigroup G H f → is-equiv-hom-Semigroup G H f
    is-equiv-is-iso-hom-Semigroup (f , μ-f) ((g , μ-g) , S , R) =
      is-equiv-is-invertible g
        ( htpy-eq (ap pr1 S))
        ( htpy-eq (ap pr1 R))

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
