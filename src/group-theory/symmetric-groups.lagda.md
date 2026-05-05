# Symmetric groups

```agda
module group-theory.symmetric-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.groups
open import group-theory.homomorphisms-groups
open import group-theory.homomorphisms-semigroups
open import group-theory.isomorphisms-groups
open import group-theory.monoids
open import group-theory.opposite-groups
open import group-theory.semigroups
open import group-theory.symmetric-concrete-groups
```

</details>

## Definitions

```agda
set-symmetric-Group : {l : Level} (X : Set l) → Set l
set-symmetric-Group X = Aut-Set X

type-symmetric-Group : {l : Level} (X : Set l) → UU l
type-symmetric-Group X = type-Set (set-symmetric-Group X)

is-set-type-symmetric-Group :
  {l : Level} (X : Set l) → is-set (type-symmetric-Group X)
is-set-type-symmetric-Group X = is-set-type-Set (set-symmetric-Group X)

has-associative-mul-aut-Set :
  {l : Level} (X : Set l) → has-associative-mul-Set (Aut-Set X)
pr1 (has-associative-mul-aut-Set X) f e = f ∘e e
pr2 (has-associative-mul-aut-Set X) e f g = associative-comp-equiv g f e

symmetric-Semigroup :
  {l : Level} (X : Set l) → Semigroup l
pr1 (symmetric-Semigroup X) = set-symmetric-Group X
pr2 (symmetric-Semigroup X) = has-associative-mul-aut-Set X

is-unital-Semigroup-symmetric-Semigroup :
  {l : Level} (X : Set l) → is-unital-Semigroup (symmetric-Semigroup X)
pr1 (is-unital-Semigroup-symmetric-Semigroup X) = id-equiv
pr1 (pr2 (is-unital-Semigroup-symmetric-Semigroup X)) = left-unit-law-equiv
pr2 (pr2 (is-unital-Semigroup-symmetric-Semigroup X)) = right-unit-law-equiv

is-group-symmetric-Semigroup' :
  {l : Level} (X : Set l) →
  is-group-is-unital-Semigroup
    ( symmetric-Semigroup X)
    ( is-unital-Semigroup-symmetric-Semigroup X)
pr1 (is-group-symmetric-Semigroup' X) = inv-equiv
pr1 (pr2 (is-group-symmetric-Semigroup' X)) = left-inverse-law-equiv
pr2 (pr2 (is-group-symmetric-Semigroup' X)) = right-inverse-law-equiv

symmetric-Group :
  {l : Level} → Set l → Group l
pr1 (symmetric-Group X) = symmetric-Semigroup X
pr1 (pr2 (symmetric-Group X)) = is-unital-Semigroup-symmetric-Semigroup X
pr2 (pr2 (symmetric-Group X)) = is-group-symmetric-Semigroup' X
```

## Properties

### If two sets are equivalent, then their symmetric groups are isomorphic

```agda
module _
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) (e : type-Set X ≃ type-Set Y)
  where

  hom-symmetric-group-equiv-Set :
    hom-Group (symmetric-Group X) (symmetric-Group Y)
  pr1 hom-symmetric-group-equiv-Set f = e ∘e (f ∘e inv-equiv e)
  pr2 hom-symmetric-group-equiv-Set {f} {g} =
    ( eq-equiv-eq-map-equiv refl) ∙
    ( ap
      ( λ h → e ∘e f ∘e h ∘e g ∘e inv-equiv e)
      ( inv (left-inverse-law-equiv e))) ∙
    ( eq-equiv-eq-map-equiv refl)

  hom-inv-symmetric-group-equiv-Set :
    hom-Group (symmetric-Group Y) (symmetric-Group X)
  pr1 hom-inv-symmetric-group-equiv-Set f = inv-equiv e ∘e f ∘e e
  pr2 hom-inv-symmetric-group-equiv-Set {f} {g} =
    ( eq-equiv-eq-map-equiv refl) ∙
    ( ap
      ( λ h → inv-equiv e ∘e f ∘e h ∘e g ∘e e)
      ( inv (right-inverse-law-equiv e))) ∙
    ( eq-equiv-eq-map-equiv refl)

  is-section-hom-inv-symmetric-group-equiv-Set :
    comp-hom-Group
      ( symmetric-Group Y)
      ( symmetric-Group X)
      ( symmetric-Group Y)
      ( hom-symmetric-group-equiv-Set)
      ( hom-inv-symmetric-group-equiv-Set) ＝
    id-hom-Group (symmetric-Group Y)
  is-section-hom-inv-symmetric-group-equiv-Set =
    eq-type-subtype
      ( preserves-mul-prop-Semigroup
        ( semigroup-Group (symmetric-Group Y))
        ( semigroup-Group (symmetric-Group Y)))
      ( eq-htpy
        ( λ f →
          ( eq-equiv-eq-map-equiv refl) ∙
          ( ap (λ h → h ∘e f ∘e h) (right-inverse-law-equiv e)) ∙
          ( eq-equiv-eq-map-equiv refl)))

  is-retraction-hom-inv-symmetric-group-equiv-Set :
    comp-hom-Group
      ( symmetric-Group X)
      ( symmetric-Group Y)
      ( symmetric-Group X)
      ( hom-inv-symmetric-group-equiv-Set)
      ( hom-symmetric-group-equiv-Set) ＝
    id-hom-Group (symmetric-Group X)
  is-retraction-hom-inv-symmetric-group-equiv-Set =
    eq-type-subtype
      ( preserves-mul-prop-Semigroup
        ( semigroup-Group (symmetric-Group X))
        ( semigroup-Group (symmetric-Group X)))
      ( eq-htpy
        ( λ f →
          ( eq-equiv-eq-map-equiv refl) ∙
          ( ap (λ h → h ∘e f ∘e h) (left-inverse-law-equiv e)) ∙
          ( eq-equiv-eq-map-equiv refl)))

  iso-symmetric-group-equiv-Set :
    iso-Group (symmetric-Group X) (symmetric-Group Y)
  pr1 iso-symmetric-group-equiv-Set =
    hom-symmetric-group-equiv-Set
  pr1 (pr2 iso-symmetric-group-equiv-Set) =
    hom-inv-symmetric-group-equiv-Set
  pr1 (pr2 (pr2 iso-symmetric-group-equiv-Set)) =
    is-section-hom-inv-symmetric-group-equiv-Set
  pr2 (pr2 (pr2 iso-symmetric-group-equiv-Set)) =
    is-retraction-hom-inv-symmetric-group-equiv-Set
```

### The symmetric group and the abstract automorphism group of a set are isomorphic

```agda
module _
  {l1 : Level} (A : Set l1)
  where

  equiv-compute-symmetric-Concrete-Group :
    type-Concrete-Group (symmetric-Concrete-Group A) ≃ type-symmetric-Group A
  equiv-compute-symmetric-Concrete-Group =
    extensionality-classifying-type-symmetric-Concrete-Group A
      ( shape-symmetric-Concrete-Group A)
      ( shape-symmetric-Concrete-Group A)

  map-compute-symmetric-Concrete-Group :
    type-Concrete-Group (symmetric-Concrete-Group A) → type-symmetric-Group A
  map-compute-symmetric-Concrete-Group =
    equiv-eq-classifying-type-symmetric-Concrete-Group A
      ( shape-symmetric-Concrete-Group A)
      ( shape-symmetric-Concrete-Group A)

  preserves-mul-compute-symmetric-Concrete-Group :
    preserves-mul-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
      ( map-compute-symmetric-Concrete-Group)
  preserves-mul-compute-symmetric-Concrete-Group {x} {y} =
    preserves-mul-equiv-eq-classifying-type-symmetric-Concrete-Group A
      ( shape-symmetric-Concrete-Group A)
      ( shape-symmetric-Concrete-Group A)
      ( shape-symmetric-Concrete-Group A)
      ( x)
      ( y)

  equiv-group-compute-symmetric-Concrete-Group :
    equiv-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
  pr1 equiv-group-compute-symmetric-Concrete-Group =
    equiv-compute-symmetric-Concrete-Group
  pr2 equiv-group-compute-symmetric-Concrete-Group {x} {y} =
    preserves-mul-compute-symmetric-Concrete-Group {x} {y}

  compute-symmetric-Concrete-Group' :
    iso-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
  compute-symmetric-Concrete-Group' =
    iso-equiv-Group
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
      ( equiv-group-compute-symmetric-Concrete-Group)

  compute-symmetric-Concrete-Group :
    iso-Group
      ( group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
  compute-symmetric-Concrete-Group =
    comp-iso-Group
      ( group-Concrete-Group (symmetric-Concrete-Group A))
      ( op-group-Concrete-Group (symmetric-Concrete-Group A))
      ( symmetric-Group A)
      ( compute-symmetric-Concrete-Group')
      ( iso-inv-Group (group-Concrete-Group (symmetric-Concrete-Group A)))
```
