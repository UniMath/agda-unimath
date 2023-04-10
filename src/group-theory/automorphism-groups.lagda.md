# Automorphism groups

```agda
module group-theory.automorphism-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.connected-components
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import group-theory.concrete-groups
open import group-theory.equivalences-concrete-groups

open import higher-group-theory.equivalences-higher-groups
open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

The automorphim group of `a : A` is the group of symmetries of `a` in `A`.

## Definitions

### Automorphism ∞-groups of a type

```agda
module _
  {l : Level} (A : UU l) (a : A)
  where

  classifying-type-Automorphism-∞-Group : UU l
  classifying-type-Automorphism-∞-Group = connected-component A a

  shape-Automorphism-∞-Group : classifying-type-Automorphism-∞-Group
  pr1 shape-Automorphism-∞-Group = a
  pr2 shape-Automorphism-∞-Group = unit-trunc-Prop refl

  classifying-pointed-type-Automorphism-∞-Group : Pointed-Type l
  pr1 classifying-pointed-type-Automorphism-∞-Group =
    classifying-type-Automorphism-∞-Group
  pr2 classifying-pointed-type-Automorphism-∞-Group =
    shape-Automorphism-∞-Group

  is-0-connected-classifying-type-Automorphism-∞-Group :
    is-0-connected classifying-type-Automorphism-∞-Group
  is-0-connected-classifying-type-Automorphism-∞-Group =
    is-0-connected-connected-component A a

  Automorphism-∞-Group : ∞-Group l
  pr1 Automorphism-∞-Group = classifying-pointed-type-Automorphism-∞-Group
  pr2 Automorphism-∞-Group =
    is-0-connected-classifying-type-Automorphism-∞-Group
```

### Automorphism groups of objects in a 1-type

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  classifying-type-Automorphism-Group : UU l
  classifying-type-Automorphism-Group =
    classifying-type-Automorphism-∞-Group (type-1-Type A) a

  shape-Automorphism-Group : classifying-type-Automorphism-Group
  shape-Automorphism-Group = shape-Automorphism-∞-Group (type-1-Type A) a

  Automorphism-Group : Concrete-Group l
  pr1 Automorphism-Group = Automorphism-∞-Group (type-1-Type A) a
  pr2 Automorphism-Group =
    is-trunc-connected-component
      ( type-1-Type A)
      ( a)
      ( is-1-type-type-1-Type A)
      ( pair a (unit-trunc-Prop refl))
      ( pair a (unit-trunc-Prop refl))

  ∞-group-Automorphism-Group : ∞-Group l
  ∞-group-Automorphism-Group = ∞-group-Concrete-Group Automorphism-Group
```

## Properties

### Characerizing the identity type of `Automorphism-∞-Group`

```agda
module _
  {l : Level} {A : UU l} (a : A)
  where

  Eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) → UU l
  Eq-classifying-type-Automorphism-∞-Group X Y = pr1 X ＝ pr1 Y

  refl-Eq-classifying-type-Automorphism-∞-Group :
    (X : classifying-type-Automorphism-∞-Group A a) →
    Eq-classifying-type-Automorphism-∞-Group X X
  refl-Eq-classifying-type-Automorphism-∞-Group X = refl

  is-contr-total-Eq-classifying-type-Automorphism-∞-Group :
    (X : classifying-type-Automorphism-∞-Group A a) →
    is-contr
      ( Σ ( classifying-type-Automorphism-∞-Group A a)
          ( Eq-classifying-type-Automorphism-∞-Group X))
  is-contr-total-Eq-classifying-type-Automorphism-∞-Group X =
    is-contr-total-Eq-subtype
      ( is-contr-total-path (pr1 X))
      ( λ a → is-prop-type-trunc-Prop)
      ( pr1 X)
      ( refl)
      ( pr2 X)

  Eq-eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    (X ＝ Y) → Eq-classifying-type-Automorphism-∞-Group X Y
  Eq-eq-classifying-type-Automorphism-∞-Group X .X refl =
    refl-Eq-classifying-type-Automorphism-∞-Group X

  is-equiv-Eq-eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    is-equiv (Eq-eq-classifying-type-Automorphism-∞-Group X Y)
  is-equiv-Eq-eq-classifying-type-Automorphism-∞-Group X =
    fundamental-theorem-id
      ( is-contr-total-Eq-classifying-type-Automorphism-∞-Group X)
      ( Eq-eq-classifying-type-Automorphism-∞-Group X)

  extensionality-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    (X ＝ Y) ≃ Eq-classifying-type-Automorphism-∞-Group X Y
  pr1 (extensionality-classifying-type-Automorphism-∞-Group X Y) =
    Eq-eq-classifying-type-Automorphism-∞-Group X Y
  pr2 (extensionality-classifying-type-Automorphism-∞-Group X Y) =
    is-equiv-Eq-eq-classifying-type-Automorphism-∞-Group X Y

  eq-Eq-classifying-type-Automorphism-∞-Group :
    (X Y : classifying-type-Automorphism-∞-Group A a) →
    Eq-classifying-type-Automorphism-∞-Group X Y → X ＝ Y
  eq-Eq-classifying-type-Automorphism-∞-Group X Y =
    map-inv-equiv (extensionality-classifying-type-Automorphism-∞-Group X Y)
```

### Characerizing the identity type of `Automorphism-Group`

```agda
module _
  {l : Level} (A : 1-Type l) (a : type-1-Type A)
  where

  Eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) → UU l
  Eq-classifying-type-Automorphism-Group =
    Eq-classifying-type-Automorphism-∞-Group a

  refl-Eq-classifying-type-Automorphism-Group :
    (X : classifying-type-Automorphism-Group A a) →
    Eq-classifying-type-Automorphism-Group X X
  refl-Eq-classifying-type-Automorphism-Group =
    refl-Eq-classifying-type-Automorphism-∞-Group a

  is-contr-total-Eq-classifying-type-Automorphism-Group :
    (X : classifying-type-Automorphism-Group A a) →
    is-contr
      ( Σ ( classifying-type-Automorphism-Group A a)
          ( Eq-classifying-type-Automorphism-Group X))
  is-contr-total-Eq-classifying-type-Automorphism-Group =
    is-contr-total-Eq-classifying-type-Automorphism-∞-Group a

  Eq-eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    (X ＝ Y) → Eq-classifying-type-Automorphism-Group X Y
  Eq-eq-classifying-type-Automorphism-Group X .X refl =
    refl-Eq-classifying-type-Automorphism-Group X

  is-equiv-Eq-eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    is-equiv (Eq-eq-classifying-type-Automorphism-Group X Y)
  is-equiv-Eq-eq-classifying-type-Automorphism-Group X =
    fundamental-theorem-id
      ( is-contr-total-Eq-classifying-type-Automorphism-Group X)
      ( Eq-eq-classifying-type-Automorphism-Group X)

  extensionality-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    (X ＝ Y) ≃ Eq-classifying-type-Automorphism-Group X Y
  pr1 (extensionality-classifying-type-Automorphism-Group X Y) =
    Eq-eq-classifying-type-Automorphism-Group X Y
  pr2 (extensionality-classifying-type-Automorphism-Group X Y) =
    is-equiv-Eq-eq-classifying-type-Automorphism-Group X Y

  eq-Eq-classifying-type-Automorphism-Group :
    (X Y : classifying-type-Automorphism-Group A a) →
    Eq-classifying-type-Automorphism-Group X Y → X ＝ Y
  eq-Eq-classifying-type-Automorphism-Group X Y =
    map-inv-equiv (extensionality-classifying-type-Automorphism-Group X Y)
```

### Equal elements have equivalent automorphism ∞-groups

```agda
module _
  {l : Level} {A : UU l}
  where

  equiv-eq-Automorphism-∞-Group :
    {x y : A} (p : x ＝ y) →
    equiv-∞-Group (Automorphism-∞-Group A x) (Automorphism-∞-Group A y)
  equiv-eq-Automorphism-∞-Group refl =
    id-equiv-∞-Group (Automorphism-∞-Group A _)
```

### Equal elements in a 1-type have isomorphic automorphism groups

```agda
module _
  {l : Level} (A : 1-Type l)
  where

  equiv-eq-Automorphism-Group :
    {x y : type-1-Type A} (p : x ＝ y) →
    equiv-Concrete-Group (Automorphism-Group A x) (Automorphism-Group A y)
  equiv-eq-Automorphism-Group refl =
    id-equiv-Concrete-Group (Automorphism-Group A _)
```
