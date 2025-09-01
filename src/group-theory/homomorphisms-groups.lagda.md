# Homomorphisms of groups

```agda
module group-theory.homomorphisms-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-monoids
open import group-theory.homomorphisms-semigroups
```

</details>

## Idea

A **group homomorphism** from one [group](group-theory.groups.md) to another is
a [semigroup homomorphism](group-theory.homomorphisms-semigroups.md) between
their underlying [semigroups](group-theory.semigroups.md).

## Definition

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-mul-Group : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group f =
    preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H) f

  preserves-mul-Group' : (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-mul-Group' f =
    preserves-mul-Semigroup' (semigroup-Group G) (semigroup-Group H) f

  is-prop-preserves-mul-Group :
    (f : type-Group G → type-Group H) → is-prop (preserves-mul-Group f)
  is-prop-preserves-mul-Group =
    is-prop-preserves-mul-Semigroup (semigroup-Group G) (semigroup-Group H)

  preserves-mul-prop-Group : (type-Group G → type-Group H) → Prop (l1 ⊔ l2)
  preserves-mul-prop-Group =
    preserves-mul-prop-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-Group : UU (l1 ⊔ l2)
  hom-Group =
    hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  map-hom-Group : hom-Group → type-Group G → type-Group H
  map-hom-Group = pr1

  preserves-mul-hom-Group :
    (f : hom-Group) →
    preserves-mul-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( map-hom-Group f)
  preserves-mul-hom-Group = pr2
```

### The identity group homomorphism

```agda
id-hom-Group : {l : Level} (G : Group l) → hom-Group G G
id-hom-Group G = id-hom-Semigroup (semigroup-Group G)
```

### Composition of group homomorphisms

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (H : Group l2) (K : Group l3)
  (g : hom-Group H K) (f : hom-Group G H)
  where

  comp-hom-Group : hom-Group G K
  comp-hom-Group =
    comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( g)
      ( f)

  map-comp-hom-Group : type-Group G → type-Group K
  map-comp-hom-Group =
    map-comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( g)
      ( f)

  preserves-mul-comp-hom-Group :
    preserves-mul-Group G K map-comp-hom-Group
  preserves-mul-comp-hom-Group =
    preserves-mul-comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( g)
      ( f)
```

## Properties

### Characterization of the identity type of group homomorphisms

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  htpy-hom-Group : (f g : hom-Group G H) → UU (l1 ⊔ l2)
  htpy-hom-Group = htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  refl-htpy-hom-Group : (f : hom-Group G H) → htpy-hom-Group f f
  refl-htpy-hom-Group =
    refl-htpy-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  htpy-eq-hom-Group : (f g : hom-Group G H) → f ＝ g → htpy-hom-Group f g
  htpy-eq-hom-Group =
    htpy-eq-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)

  abstract
    is-torsorial-htpy-hom-Group :
      ( f : hom-Group G H) → is-torsorial (htpy-hom-Group f)
    is-torsorial-htpy-hom-Group =
      is-torsorial-htpy-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  abstract
    is-equiv-htpy-eq-hom-Group :
      (f g : hom-Group G H) → is-equiv (htpy-eq-hom-Group f g)
    is-equiv-htpy-eq-hom-Group =
      is-equiv-htpy-eq-hom-Semigroup
        ( semigroup-Group G)
        ( semigroup-Group H)

  extensionality-hom-Group :
    (f g : hom-Group G H) → (f ＝ g) ≃ htpy-hom-Group f g
  pr1 (extensionality-hom-Group f g) = htpy-eq-hom-Group f g
  pr2 (extensionality-hom-Group f g) = is-equiv-htpy-eq-hom-Group f g

  eq-htpy-hom-Group : {f g : hom-Group G H} → htpy-hom-Group f g → f ＝ g
  eq-htpy-hom-Group =
    eq-htpy-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  is-set-hom-Group : is-set (hom-Group G H)
  is-set-hom-Group =
    is-set-hom-Semigroup (semigroup-Group G) (semigroup-Group H)

  hom-set-Group : Set (l1 ⊔ l2)
  pr1 hom-set-Group = hom-Group G H
  pr2 hom-set-Group = is-set-hom-Group
```

### Associativity of composition of group homomorphisms

```agda
module _
  {l1 l2 l3 l4 : Level}
  (G : Group l1) (H : Group l2) (K : Group l3) (L : Group l4)
  where

  associative-comp-hom-Group :
    (h : hom-Group K L) (g : hom-Group H K) (f : hom-Group G H) →
    comp-hom-Group G H L (comp-hom-Group H K L h g) f ＝
    comp-hom-Group G K L h (comp-hom-Group G H K g f)
  associative-comp-hom-Group =
    associative-comp-hom-Semigroup
      ( semigroup-Group G)
      ( semigroup-Group H)
      ( semigroup-Group K)
      ( semigroup-Group L)
```

### The left and right unit laws for composition of group homomorphisms

```agda
left-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  comp-hom-Group G H H (id-hom-Group H) f ＝ f
left-unit-law-comp-hom-Group G H =
  left-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)

right-unit-law-comp-hom-Group :
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H) →
  comp-hom-Group G G H f (id-hom-Group G) ＝ f
right-unit-law-comp-hom-Group G H =
  right-unit-law-comp-hom-Semigroup
    ( semigroup-Group G)
    ( semigroup-Group H)
```

### Group homomorphisms preserve the unit element

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-unit-Group : (type-Group G → type-Group H) → UU l2
  preserves-unit-Group f = f (unit-Group G) ＝ unit-Group H

  abstract
    preserves-unit-hom-Group :
      ( f : hom-Group G H) → preserves-unit-Group (map-hom-Group G H f)
    preserves-unit-hom-Group f =
      ( inv (left-unit-law-mul-Group H (map-hom-Group G H f (unit-Group G)))) ∙
      ( ap
        ( λ x → mul-Group H x (map-hom-Group G H f (unit-Group G)))
        ( inv
          ( left-inverse-law-mul-Group H
            ( map-hom-Group G H f (unit-Group G))))) ∙
      ( associative-mul-Group H
        ( inv-Group H (map-hom-Group G H f (unit-Group G)))
        ( map-hom-Group G H f (unit-Group G))
        ( map-hom-Group G H f (unit-Group G))) ∙
      ( ap
        ( mul-Group H (inv-Group H (map-hom-Group G H f (unit-Group G))))
        ( inv (preserves-mul-hom-Group G H f))) ∙
      ( ap
        ( λ x →
          mul-Group H
            ( inv-Group H (map-hom-Group G H f (unit-Group G)))
            ( map-hom-Group G H f x))
        ( left-unit-law-mul-Group G (unit-Group G))) ∙
      ( left-inverse-law-mul-Group H (map-hom-Group G H f (unit-Group G)))
```

### Group homomorphisms preserve inverses

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  preserves-inverses-Group :
    (type-Group G → type-Group H) → UU (l1 ⊔ l2)
  preserves-inverses-Group f =
    {x : type-Group G} → Id (f (inv-Group G x)) (inv-Group H (f x))

  abstract
    preserves-inv-hom-Group :
      (f : hom-Group G H) → preserves-inverses-Group (map-hom-Group G H f)
    preserves-inv-hom-Group f {x} =
      ( inv
        ( right-unit-law-mul-Group H (map-hom-Group G H f (inv-Group G x)))) ∙
      ( ap
        ( mul-Group H (map-hom-Group G H f (inv-Group G x)))
        ( inv (right-inverse-law-mul-Group H (map-hom-Group G H f x)))) ∙
      ( inv
        ( associative-mul-Group H
          ( map-hom-Group G H f (inv-Group G x))
          ( map-hom-Group G H f x)
          ( inv-Group H (map-hom-Group G H f x)))) ∙
      ( inv
        ( ap
          ( λ y → mul-Group H y (inv-Group H (map-hom-Group G H f x)))
          ( preserves-mul-hom-Group G H f))) ∙
      ( ap
        ( λ y →
          mul-Group H
            ( map-hom-Group G H f y)
            ( inv-Group H (map-hom-Group G H f x)))
        ( left-inverse-law-mul-Group G x)) ∙
      ( ap
        ( λ y → mul-Group H y (inv-Group H (map-hom-Group G H f x)))
        ( preserves-unit-hom-Group G H f)) ∙
      ( left-unit-law-mul-Group H (inv-Group H (map-hom-Group G H f x)))
```

### Group homomorphisms preserve all group structure

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2)
  where

  hom-Group' : UU (l1 ⊔ l2)
  hom-Group' =
    Σ ( hom-Group G H)
      ( λ f →
        ( preserves-unit-Group G H (map-hom-Group G H f)) ×
        ( preserves-inverses-Group G H (map-hom-Group G H f)))

  preserves-group-structure-hom-Group :
    hom-Group G H → hom-Group'
  pr1 (preserves-group-structure-hom-Group f) = f
  pr1 (pr2 (preserves-group-structure-hom-Group f)) =
    preserves-unit-hom-Group G H f
  pr2 (pr2 (preserves-group-structure-hom-Group f)) =
    preserves-inv-hom-Group G H f
```

### Group homomorphisms induce monoid homomorphisms between the underlying monoids

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  hom-monoid-hom-Group : hom-Monoid (monoid-Group G) (monoid-Group H)
  pr1 hom-monoid-hom-Group = f
  pr2 hom-monoid-hom-Group = preserves-unit-hom-Group G H f
```

### Group homomorphisms preserve left and right division

```agda
module _
  {l1 l2 : Level} (G : Group l1) (H : Group l2) (f : hom-Group G H)
  where

  preserves-left-div-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (left-div-Group G x y) ＝
    left-div-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-left-div-hom-Group =
    ( preserves-mul-hom-Group G H f) ∙
    ( ap (mul-Group' H _) (preserves-inv-hom-Group G H f))

  preserves-right-div-hom-Group :
    {x y : type-Group G} →
    map-hom-Group G H f (right-div-Group G x y) ＝
    right-div-Group H (map-hom-Group G H f x) (map-hom-Group G H f y)
  preserves-right-div-hom-Group =
    ( preserves-mul-hom-Group G H f) ∙
    ( ap (mul-Group H _) (preserves-inv-hom-Group G H f))
```
