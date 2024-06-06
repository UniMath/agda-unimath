# Homomorphisms of group actions

```agda
module group-theory.homomorphisms-group-actions where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import group-theory.group-actions
open import group-theory.groups
```

</details>

## Idea

A **morphism of group actions** from a [`G`-set](group-theory.group-actions.md)
`X` to a `G`-set `Y` is a map from the underlying [set](foundation-core.sets.md)
of `X` to the underlying set of `Y` **preserving the group action**. This means
that for any element `g` of the [group](group-theory.groups.md) `G` the square

```text
          f
      X ─────> Y
      │        │
  μ g │        │ μ g
      ∨        ∨
      X ─────> Y
          f
```

[commutes](foundation-core.commuting-squares-of-maps.md).

## Definitions

### The predicate on maps between underlying types of group actions to preserve the group action

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  (f : type-action-Group G X → type-action-Group G Y)
  where

  preserves-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  preserves-action-Group =
    (g : type-Group G) →
    coherence-square-maps f (mul-action-Group G X g) (mul-action-Group G Y g) f

  is-prop-preserves-action-Group : is-prop preserves-action-Group
  is-prop-preserves-action-Group =
    is-prop-iterated-Π 2
      ( λ g x →
        is-set-type-action-Group G Y
          ( f (mul-action-Group G X g x))
          ( mul-action-Group G Y g (f x)))

  preserves-action-prop-Group : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 preserves-action-prop-Group = preserves-action-Group
  pr2 preserves-action-prop-Group = is-prop-preserves-action-Group
```

### Morphisms of `G`-sets

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3)
  where

  hom-action-Group : UU (l1 ⊔ l2 ⊔ l3)
  hom-action-Group =
    Σ ( type-action-Group G X → type-action-Group G Y)
      ( preserves-action-Group G X Y)

  map-hom-action-Group :
    hom-action-Group → type-action-Group G X → type-action-Group G Y
  map-hom-action-Group = pr1

  preserves-action-hom-action-Group :
    (f : hom-action-Group) →
    preserves-action-Group G X Y (map-hom-action-Group f)
  preserves-action-hom-action-Group = pr2
```

### The identity morphism

```agda
module _
  {l1 l2 : Level} (G : Group l1) (X : action-Group G l2)
  where

  id-hom-action-Group : hom-action-Group G X X
  pr1 id-hom-action-Group = id
  pr2 id-hom-action-Group g = refl-htpy
```

### Composition of morphisms

```agda
module _
  {l1 l2 l3 l4 : Level} (G : Group l1)
  (X : action-Group G l2) (Y : action-Group G l3) (Z : action-Group G l4)
  where

  map-comp-hom-action-Group :
    hom-action-Group G Y Z → hom-action-Group G X Y →
    type-action-Group G X → type-action-Group G Z
  map-comp-hom-action-Group g f =
    map-hom-action-Group G Y Z g ∘ map-hom-action-Group G X Y f

  preserves-action-comp-hom-action-Group :
    (g : hom-action-Group G Y Z) (f : hom-action-Group G X Y) →
    preserves-action-Group G X Z (map-comp-hom-action-Group g f)
  preserves-action-comp-hom-action-Group g f x =
    pasting-horizontal-coherence-square-maps
      ( map-hom-action-Group G X Y f)
      ( map-hom-action-Group G Y Z g)
      ( mul-action-Group G X x)
      ( mul-action-Group G Y x)
      ( mul-action-Group G Z x)
      ( map-hom-action-Group G X Y f)
      ( map-hom-action-Group G Y Z g)
      ( preserves-action-hom-action-Group G X Y f x)
      ( preserves-action-hom-action-Group G Y Z g x)

  comp-hom-action-Group :
    hom-action-Group G Y Z → hom-action-Group G X Y → hom-action-Group G X Z
  pr1 (comp-hom-action-Group g f) = map-comp-hom-action-Group g f
  pr2 (comp-hom-action-Group g f) = preserves-action-comp-hom-action-Group g f
```

## Properties

### Equality of homomorphisms of group actions is equivalent to homotopies

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3) (f : hom-action-Group G X Y)
  where

  htpy-hom-action-Group :
    (g : hom-action-Group G X Y) → UU (l2 ⊔ l3)
  htpy-hom-action-Group g =
    map-hom-action-Group G X Y f ~ map-hom-action-Group G X Y g

  refl-htpy-hom-action-Group : htpy-hom-action-Group f
  refl-htpy-hom-action-Group = refl-htpy

  htpy-eq-hom-action-Group :
    (g : hom-action-Group G X Y) →
    f ＝ g → htpy-hom-action-Group g
  htpy-eq-hom-action-Group .f refl =
    refl-htpy-hom-action-Group

  is-torsorial-htpy-hom-action-Group :
    is-torsorial htpy-hom-action-Group
  is-torsorial-htpy-hom-action-Group =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (map-hom-action-Group G X Y f))
      ( λ g →
        is-prop-Π
          ( λ x →
            is-prop-Π
              ( λ y →
                is-set-type-Set
                  ( set-action-Group G Y)
                  ( g (mul-action-Group G X x y))
                  ( mul-action-Group G Y x (g y)))))
      ( map-hom-action-Group G X Y f)
      ( refl-htpy)
      ( preserves-action-hom-action-Group G X Y f)

  is-equiv-htpy-eq-hom-action-Group :
    (g : hom-action-Group G X Y) → is-equiv (htpy-eq-hom-action-Group g)
  is-equiv-htpy-eq-hom-action-Group =
    fundamental-theorem-id
      is-torsorial-htpy-hom-action-Group
      htpy-eq-hom-action-Group

  extensionality-hom-action-Group :
    (g : hom-action-Group G X Y) → (f ＝ g) ≃ htpy-hom-action-Group g
  pr1 (extensionality-hom-action-Group g) =
    htpy-eq-hom-action-Group g
  pr2 (extensionality-hom-action-Group g) =
    is-equiv-htpy-eq-hom-action-Group g

  eq-htpy-hom-action-Group :
    (g : hom-action-Group G X Y) → htpy-hom-action-Group g → f ＝ g
  eq-htpy-hom-action-Group g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-action-Group g)
```

### The type of morphisms of group actions is a set

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3)
  where

  is-set-hom-action-Group :
    is-set (hom-action-Group G X Y)
  is-set-hom-action-Group f g =
    is-prop-equiv
      ( extensionality-hom-action-Group G X Y f g)
      ( is-prop-Π
        ( λ x →
          is-set-type-action-Group G Y
            ( map-hom-action-Group G X Y f x)
            ( map-hom-action-Group G X Y g x)))

  hom-set-action-Group : Set (l1 ⊔ l2 ⊔ l3)
  pr1 hom-set-action-Group = hom-action-Group G X Y
  pr2 hom-set-action-Group = is-set-hom-action-Group
```

### Composition is associative

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (G : Group l1)
  (X1 : action-Group G l2) (X2 : action-Group G l3)
  (X3 : action-Group G l4) (X4 : action-Group G l5)
  (h : hom-action-Group G X3 X4)
  (g : hom-action-Group G X2 X3)
  (f : hom-action-Group G X1 X2)
  where

  associative-comp-hom-action-Group :
    comp-hom-action-Group G X1 X2 X4 (comp-hom-action-Group G X2 X3 X4 h g) f ＝
    comp-hom-action-Group G X1 X3 X4 h (comp-hom-action-Group G X1 X2 X3 g f)
  associative-comp-hom-action-Group =
    eq-htpy-hom-action-Group G X1 X4
      ( comp-hom-action-Group G X1 X2 X4
        ( comp-hom-action-Group G X2 X3 X4 h g)
        ( f))
      ( comp-hom-action-Group G X1 X3 X4
        ( h)
        ( comp-hom-action-Group G X1 X2 X3 g f))
      ( refl-htpy)
```

### Composition satisfies the left and right unit laws

```agda
module _
  {l1 l2 l3 : Level} (G : Group l1) (X : action-Group G l2)
  (Y : action-Group G l3)
  where

  left-unit-law-comp-hom-action-Group :
    (f : hom-action-Group G X Y) →
    comp-hom-action-Group G X Y Y (id-hom-action-Group G Y) f ＝ f
  left-unit-law-comp-hom-action-Group f =
    eq-htpy-hom-action-Group G X Y
      ( comp-hom-action-Group G X Y Y (id-hom-action-Group G Y) f)
      ( f)
      ( refl-htpy)

  right-unit-law-comp-hom-action-Group :
    (f : hom-action-Group G X Y) →
    comp-hom-action-Group G X X Y f (id-hom-action-Group G X) ＝ f
  right-unit-law-comp-hom-action-Group f =
    eq-htpy-hom-action-Group G X Y
      ( comp-hom-action-Group G X X Y f (id-hom-action-Group G X))
      ( f)
      ( refl-htpy)
```
