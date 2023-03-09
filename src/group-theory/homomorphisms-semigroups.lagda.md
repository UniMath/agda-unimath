# Homomorphisms of semigroups

```agda
module group-theory.homomorphisms-semigroups where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

A homomorphism between two semigroups is a map between their underlying types that preserves the binary operation.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  preserves-mul : (μA : A → A → A) (μB : B → B → B) → (A → B) → UU (l1 ⊔ l2)
  preserves-mul μA μB f = (x y : A) → Id (f (μA x y)) (μB (f x) (f y))

module _
  {l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  where

  preserves-mul-semigroup-Prop :
    (type-Semigroup G → type-Semigroup H) → Prop (l1 ⊔ l2)
  preserves-mul-semigroup-Prop f =
    Π-Prop
      ( type-Semigroup G)
      ( λ x →
        Π-Prop
          ( type-Semigroup G)
          ( λ y →
            Id-Prop
              ( set-Semigroup H)
              ( f (mul-Semigroup G x y))
              ( mul-Semigroup H (f x) (f y))))

  preserves-mul-semigroup-Prop' :
    (type-Semigroup G → type-Semigroup H) → Prop (l1 ⊔ l2)
  preserves-mul-semigroup-Prop' f =
    Π-Prop
      ( type-Semigroup G)
      ( λ x →
        Π-Prop
          ( type-Semigroup G)
          ( λ y →
            Id-Prop
              ( set-Semigroup H)
              ( f (mul-Semigroup' G x y))
              ( mul-Semigroup H (f x) (f y))))

  preserves-mul-Semigroup :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup f =
    type-Prop (preserves-mul-semigroup-Prop f)

  preserves-mul-Semigroup' :
    (type-Semigroup G → type-Semigroup H) → UU (l1 ⊔ l2)
  preserves-mul-Semigroup' f =
    type-Prop (preserves-mul-semigroup-Prop' f)

  is-prop-preserves-mul-Semigroup :
    (f : type-Semigroup G → type-Semigroup H) →
    is-prop (preserves-mul-Semigroup f)
  is-prop-preserves-mul-Semigroup f =
    is-prop-type-Prop (preserves-mul-semigroup-Prop f)

  is-prop-preserves-mul-Semigroup' :
    (f : type-Semigroup G → type-Semigroup H) →
    is-prop (preserves-mul-Semigroup' f)
  is-prop-preserves-mul-Semigroup' f =
    is-prop-type-Prop (preserves-mul-semigroup-Prop' f)

  type-hom-Semigroup : UU (l1 ⊔ l2)
  type-hom-Semigroup =
    Σ ( type-Semigroup G → type-Semigroup H)
      ( preserves-mul-Semigroup)

  map-hom-Semigroup :
    type-hom-Semigroup → type-Semigroup G → type-Semigroup H
  map-hom-Semigroup f = pr1 f

  preserves-mul-hom-Semigroup :
    (f : type-hom-Semigroup) → preserves-mul-Semigroup (map-hom-Semigroup f)
  preserves-mul-hom-Semigroup f = pr2 f

  {- We characterize the identity type of the semigroup homomorphisms. -}

  htpy-hom-Semigroup : (f g : type-hom-Semigroup) → UU (l1 ⊔ l2)
  htpy-hom-Semigroup f g = map-hom-Semigroup f ~ map-hom-Semigroup g

  refl-htpy-hom-Semigroup : (f : type-hom-Semigroup) → htpy-hom-Semigroup f f
  refl-htpy-hom-Semigroup f = refl-htpy

  htpy-eq-hom-Semigroup :
    (f g : type-hom-Semigroup) → Id f g → htpy-hom-Semigroup f g
  htpy-eq-hom-Semigroup f .f refl = refl-htpy-hom-Semigroup f

  abstract
    is-contr-total-htpy-hom-Semigroup :
      (f : type-hom-Semigroup) →
      is-contr (Σ type-hom-Semigroup (htpy-hom-Semigroup f))
    is-contr-total-htpy-hom-Semigroup f =
      is-contr-total-Eq-subtype
        ( is-contr-total-htpy (map-hom-Semigroup f))
        ( is-prop-preserves-mul-Semigroup)
        ( map-hom-Semigroup f)
        ( refl-htpy)
        ( preserves-mul-hom-Semigroup f)

  abstract
    is-equiv-htpy-eq-hom-Semigroup :
      (f g : type-hom-Semigroup) → is-equiv (htpy-eq-hom-Semigroup f g)
    is-equiv-htpy-eq-hom-Semigroup f =
      fundamental-theorem-id
        ( is-contr-total-htpy-hom-Semigroup f)
        ( htpy-eq-hom-Semigroup f)

  eq-htpy-hom-Semigroup :
    {f g : type-hom-Semigroup} → htpy-hom-Semigroup f g → Id f g
  eq-htpy-hom-Semigroup {f} {g} =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-Semigroup f g)

  is-set-type-hom-Semigroup : is-set type-hom-Semigroup
  is-set-type-hom-Semigroup f g =
    is-prop-is-equiv
      ( is-equiv-htpy-eq-hom-Semigroup f g)
      ( is-prop-Π
        ( λ x →
          is-set-type-Semigroup H
            ( map-hom-Semigroup f x)
            ( map-hom-Semigroup g x)))

  hom-Semigroup : Set (l1 ⊔ l2)
  pr1 hom-Semigroup = type-hom-Semigroup
  pr2 hom-Semigroup = is-set-type-hom-Semigroup

preserves-mul-id-Semigroup :
  {l : Level} (G : Semigroup l) → preserves-mul-Semigroup G G id
preserves-mul-id-Semigroup G x y = refl
```

### The identity homomorphism of semigroups

```agda
id-hom-Semigroup :
  {l : Level} (G : Semigroup l) → type-hom-Semigroup G G
pr1 (id-hom-Semigroup G) = id
pr2 (id-hom-Semigroup G) = preserves-mul-id-Semigroup G
```

### Composition of morphisms of semigroups

```agda
comp-hom-Semigroup :
  {l1 l2 l3 : Level} →
  (G : Semigroup l1) (H : Semigroup l2) (K : Semigroup l3) →
  type-hom-Semigroup H K → type-hom-Semigroup G H → type-hom-Semigroup G K
pr1 (comp-hom-Semigroup G H K g f) =
  (map-hom-Semigroup H K g) ∘ (map-hom-Semigroup G H f)
pr2 (comp-hom-Semigroup G H K g f) x y =
  ( ap ( map-hom-Semigroup H K g)
       ( preserves-mul-hom-Semigroup G H f x y)) ∙
  ( preserves-mul-hom-Semigroup H K g
    ( map-hom-Semigroup G H f x)
    ( map-hom-Semigroup G H f y))
```

### Associativity of composition of homomorphisms of semigroups

```agda
associative-comp-hom-Semigroup :
  { l1 l2 l3 l4 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( K : Semigroup l3) (L : Semigroup l4) (h : type-hom-Semigroup K L) →
  ( g : type-hom-Semigroup H K) (f : type-hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G H L
       ( comp-hom-Semigroup H K L h g) f)
     ( comp-hom-Semigroup G K L h
       ( comp-hom-Semigroup G H K g f))
associative-comp-hom-Semigroup G H K L (pair h μ-h) (pair g μ-g) (pair f μ-f) =
  eq-htpy-hom-Semigroup G L refl-htpy
```

### The left and right unit laws for composition of homomorphisms of semigroups

```agda
left-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : type-hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G H H (id-hom-Semigroup H) f) f
left-unit-law-comp-hom-Semigroup G
  (pair (pair H is-set-H) (pair μ-H assoc-H)) (pair f μ-f) =
  eq-htpy-hom-Semigroup G
    ( pair (pair H is-set-H) (pair μ-H assoc-H))
    ( refl-htpy)

right-unit-law-comp-hom-Semigroup :
  { l1 l2 : Level} (G : Semigroup l1) (H : Semigroup l2)
  ( f : type-hom-Semigroup G H) →
  Id ( comp-hom-Semigroup G G H f (id-hom-Semigroup G)) f
right-unit-law-comp-hom-Semigroup
  (pair (pair G is-set-G) (pair μ-G assoc-G)) H (pair f μ-f) =
  eq-htpy-hom-Semigroup
    ( pair (pair G is-set-G) (pair μ-G assoc-G)) H refl-htpy
```
