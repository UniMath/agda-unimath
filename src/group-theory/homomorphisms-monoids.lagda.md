# Homomorphisms of monoids

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.homomorphisms-monoids
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.propositions funext
open import foundation.sets funext
open import foundation.subtype-identity-principle
open import foundation.subtypes funext
open import foundation.torsorial-type-families funext
open import foundation.universe-levels

open import group-theory.homomorphisms-semigroups funext
open import group-theory.invertible-elements-monoids funext
open import group-theory.monoids funext
```

</details>

## Idea

**Homomorphisms** between two [monoids](group-theory.monoids.md) are
[homomorphisms](group-theory.homomorphisms-semigroups.md) between their
underlying [semigroups](group-theory.semigroups.md) that preserve the unit
element.

## Definition

### Homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M1 : Monoid l1) (M2 : Monoid l2)
  where

  preserves-unit-prop-hom-Semigroup :
    hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2) → Prop l2
  preserves-unit-prop-hom-Semigroup f =
    Id-Prop
      ( set-Monoid M2)
      ( map-hom-Semigroup
        ( semigroup-Monoid M1)
        ( semigroup-Monoid M2)
        ( f)
        ( unit-Monoid M1))
      ( unit-Monoid M2)

  preserves-unit-hom-Semigroup :
    hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2) → UU l2
  preserves-unit-hom-Semigroup f =
    type-Prop (preserves-unit-prop-hom-Semigroup f)

  is-prop-preserves-unit-hom-Semigroup :
    (f : hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2)) →
    is-prop (preserves-unit-hom-Semigroup f)
  is-prop-preserves-unit-hom-Semigroup f =
    is-prop-type-Prop (preserves-unit-prop-hom-Semigroup f)

  preserves-unit-hom-prop-Semigroup :
    hom-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2) →
    Prop l2
  preserves-unit-hom-prop-Semigroup f =
    ( preserves-unit-hom-Semigroup f ,
      is-prop-preserves-unit-hom-Semigroup f)

  hom-set-Monoid : Set (l1 ⊔ l2)
  hom-set-Monoid =
    set-subset
      ( hom-set-Semigroup (semigroup-Monoid M1) (semigroup-Monoid M2))
      ( preserves-unit-prop-hom-Semigroup)

  hom-Monoid : UU (l1 ⊔ l2)
  hom-Monoid = type-Set hom-set-Monoid

module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  hom-semigroup-hom-Monoid :
    hom-Semigroup (semigroup-Monoid M) (semigroup-Monoid N)
  hom-semigroup-hom-Monoid = pr1 f

  map-hom-Monoid : type-Monoid M → type-Monoid N
  map-hom-Monoid =
    map-hom-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( hom-semigroup-hom-Monoid)

  preserves-mul-hom-Monoid :
    preserves-mul-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( map-hom-Monoid)
  preserves-mul-hom-Monoid =
    preserves-mul-hom-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( hom-semigroup-hom-Monoid)

  preserves-unit-hom-Monoid :
    preserves-unit-hom-Semigroup M N hom-semigroup-hom-Monoid
  preserves-unit-hom-Monoid = pr2 f
```

### The identity homomorphism of monoids

```agda
preserves-unit-id-hom-Monoid :
  { l : Level} (M : Monoid l) →
  preserves-unit-hom-Semigroup M M (id-hom-Semigroup (semigroup-Monoid M))
preserves-unit-id-hom-Monoid M = refl

id-hom-Monoid :
  {l : Level} (M : Monoid l) → hom-Monoid M M
pr1 (id-hom-Monoid M) = id-hom-Semigroup (semigroup-Monoid M)
pr2 (id-hom-Monoid M) = preserves-unit-id-hom-Monoid M
```

### Composition of homomorphisms of monoids

```agda
module _
  {l1 l2 l3 : Level} (K : Monoid l1) (L : Monoid l2) (M : Monoid l3)
  where

  preserves-unit-comp-hom-Monoid :
    (g : hom-Monoid L M) (f : hom-Monoid K L) →
    preserves-unit-hom-Semigroup K M
      ( comp-hom-Semigroup
        ( semigroup-Monoid K)
        ( semigroup-Monoid L)
        ( semigroup-Monoid M)
        ( hom-semigroup-hom-Monoid L M g)
        ( hom-semigroup-hom-Monoid K L f))
  preserves-unit-comp-hom-Monoid g f =
    ( ap (map-hom-Monoid L M g) (preserves-unit-hom-Monoid K L f)) ∙
    ( preserves-unit-hom-Monoid L M g)

  comp-hom-Monoid :
    hom-Monoid L M → hom-Monoid K L → hom-Monoid K M
  pr1 (comp-hom-Monoid g f) =
    comp-hom-Semigroup
      ( semigroup-Monoid K)
      ( semigroup-Monoid L)
      ( semigroup-Monoid M)
      ( hom-semigroup-hom-Monoid L M g)
      ( hom-semigroup-hom-Monoid K L f)
  pr2 (comp-hom-Monoid g f) =
    preserves-unit-comp-hom-Monoid g f
```

### Homotopies of homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  htpy-hom-Monoid : (f g : hom-Monoid M N) → UU (l1 ⊔ l2)
  htpy-hom-Monoid f g =
    htpy-hom-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( hom-semigroup-hom-Monoid M N f)
      ( hom-semigroup-hom-Monoid M N g)

  refl-htpy-hom-Monoid : (f : hom-Monoid M N) → htpy-hom-Monoid f f
  refl-htpy-hom-Monoid f =
    refl-htpy-hom-Semigroup
      ( semigroup-Monoid M)
      ( semigroup-Monoid N)
      ( hom-semigroup-hom-Monoid M N f)
```

## Properties

### Homotopies characterize identifications of homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2) (f : hom-Monoid M N)
  where

  is-torsorial-htpy-hom-Monoid :
    is-torsorial (htpy-hom-Monoid M N f)
  is-torsorial-htpy-hom-Monoid =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy-hom-Semigroup
        ( semigroup-Monoid M)
        ( semigroup-Monoid N)
        ( hom-semigroup-hom-Monoid M N f))
      ( is-prop-preserves-unit-hom-Semigroup M N)
      ( hom-semigroup-hom-Monoid M N f)
      ( refl-htpy-hom-Monoid M N f)
      ( preserves-unit-hom-Monoid M N f)

  htpy-eq-hom-Monoid :
    (g : hom-Monoid M N) → f ＝ g → htpy-hom-Monoid M N f g
  htpy-eq-hom-Monoid .f refl = refl-htpy-hom-Monoid M N f

  is-equiv-htpy-eq-hom-Monoid :
    (g : hom-Monoid M N) → is-equiv (htpy-eq-hom-Monoid g)
  is-equiv-htpy-eq-hom-Monoid =
    fundamental-theorem-id is-torsorial-htpy-hom-Monoid htpy-eq-hom-Monoid

  extensionality-hom-Monoid :
    (g : hom-Monoid M N) → (f ＝ g) ≃ htpy-hom-Monoid M N f g
  pr1 (extensionality-hom-Monoid g) = htpy-eq-hom-Monoid g
  pr2 (extensionality-hom-Monoid g) = is-equiv-htpy-eq-hom-Monoid g

  eq-htpy-hom-Monoid :
    (g : hom-Monoid M N) → htpy-hom-Monoid M N f g → f ＝ g
  eq-htpy-hom-Monoid g = map-inv-equiv (extensionality-hom-Monoid g)
```

### Associativity of composition of homomorphisms of monoids

```agda
module _
  {l1 l2 l3 l4 : Level}
  (K : Monoid l1) (L : Monoid l2) (M : Monoid l3) (N : Monoid l4)
  where

  associative-comp-hom-Monoid :
    (h : hom-Monoid M N) (g : hom-Monoid L M) (f : hom-Monoid K L) →
    comp-hom-Monoid K L N (comp-hom-Monoid L M N h g) f ＝
    comp-hom-Monoid K M N h (comp-hom-Monoid K L M g f)
  associative-comp-hom-Monoid h g f =
    eq-htpy-hom-Monoid K N
      ( comp-hom-Monoid K L N (comp-hom-Monoid L M N h g) f)
      ( comp-hom-Monoid K M N h (comp-hom-Monoid K L M g f))
      ( refl-htpy)
```

### Unit laws for composition of homomorphisms of monoids

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  where

  left-unit-law-comp-hom-Monoid :
    (f : hom-Monoid M N) →
    comp-hom-Monoid M N N (id-hom-Monoid N) f ＝ f
  left-unit-law-comp-hom-Monoid f =
    eq-htpy-hom-Monoid M N
      ( comp-hom-Monoid M N N (id-hom-Monoid N) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-Monoid :
    (f : hom-Monoid M N) →
    comp-hom-Monoid M M N f (id-hom-Monoid M) ＝ f
  right-unit-law-comp-hom-Monoid f =
    eq-htpy-hom-Monoid M N
      ( comp-hom-Monoid M M N f (id-hom-Monoid M))
      ( f)
      ( refl-htpy)
```

### Any homomorphism of monoids sends invertible elements to invertible elements

```agda
module _
  {l1 l2 : Level} (M : Monoid l1) (N : Monoid l2)
  (f : hom-Monoid M N)
  where

  preserves-invertible-elements-hom-Monoid :
    {x : type-Monoid M} →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid N (map-hom-Monoid M N f x)
  pr1 (preserves-invertible-elements-hom-Monoid (y , p , q)) =
    map-hom-Monoid M N f y
  pr1 (pr2 (preserves-invertible-elements-hom-Monoid (y , p , q))) =
    ( inv (preserves-mul-hom-Monoid M N f)) ∙
    ( ap (map-hom-Monoid M N f) p) ∙
    ( preserves-unit-hom-Monoid M N f)
  pr2 (pr2 (preserves-invertible-elements-hom-Monoid (y , p , q))) =
    ( inv (preserves-mul-hom-Monoid M N f)) ∙
    ( ap (map-hom-Monoid M N f) q) ∙
    ( preserves-unit-hom-Monoid M N f)
```
