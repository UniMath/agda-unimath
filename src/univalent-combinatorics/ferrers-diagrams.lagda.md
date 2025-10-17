# Ferrers diagrams (unlabeled partitions)

```agda
module univalent-combinatorics.ferrers-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.identity-types
open import foundation.mere-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.torsorial-type-families
open import foundation.univalence
open import foundation.universe-levels

open import univalent-combinatorics.finite-types
```

</details>

## Idea

**Unlabeled partitions**, also known as **Ferrers diagrams**, of a type `A`
record the number of ways in which `A` can be decomposed as the
[dependent pair type](foundation.dependent-pair-types.md) of a family of
[inhabited types](foundation.inhabited-types.md). More precisely, a Ferrers
diagram of a type `A` consists of a type `X` and a family `Y` of inhabited types
over `X` such that `Σ X Y` is
[merely equivalent](foundation.mere-equivalences.md) to `A`. A finite Finite
ferrers diagram of a [finite type](univalent-combinatorics.finite-types.md) `A`
consists of a finite type `X` and a family `Y` of inhabited finite types over
`X` such that `Σ X Y` is merely equivalent to `A`. The number of finite Ferrers
diagrams of `A` is the [partition number](univalent-combinatorics.partitions.md)
of the [cardinality](set-theory.cardinals.md) of `A`.

## Definition

### Ferrers diagrams of arbitrary types

```agda
ferrers-diagram :
  {l1 : Level} (l2 l3 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
ferrers-diagram l2 l3 A =
  Σ ( UU l2)
    ( λ X →
      Σ ( X → UU l3)
        ( λ Y →
          ((x : X) → type-trunc-Prop (Y x)) × mere-equiv A (Σ X Y)))

module _
  {l1 l2 l3 : Level} {A : UU l1} (D : ferrers-diagram l2 l3 A)
  where

  row-ferrers-diagram : UU l2
  row-ferrers-diagram = pr1 D

  dot-ferrers-diagram : row-ferrers-diagram → UU l3
  dot-ferrers-diagram = pr1 (pr2 D)

  is-inhabited-dot-ferrers-diagram :
    (x : row-ferrers-diagram) → type-trunc-Prop (dot-ferrers-diagram x)
  is-inhabited-dot-ferrers-diagram = pr1 (pr2 (pr2 D))

  mere-equiv-ferrers-diagram :
    mere-equiv A (Σ row-ferrers-diagram dot-ferrers-diagram)
  mere-equiv-ferrers-diagram = pr2 (pr2 (pr2 D))
```

### Finite Ferrers diagrams of finite types

```agda
ferrers-diagram-Finite-Type :
  {l1 : Level} (l2 l3 : Level) (A : Finite-Type l1) →
  UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
ferrers-diagram-Finite-Type {l} l2 l3 A =
  Σ ( Finite-Type l2)
    ( λ X →
      Σ ( type-Finite-Type X → Finite-Type l3)
        ( λ Y →
          ( (x : type-Finite-Type X) →
            type-trunc-Prop (type-Finite-Type (Y x))) ×
          mere-equiv
            ( type-Finite-Type A)
            ( Σ (type-Finite-Type X) (λ x → type-Finite-Type (Y x)))))

module _
  {l1 l2 l3 : Level} (A : Finite-Type l1)
  (D : ferrers-diagram-Finite-Type l2 l3 A)
  where

  row-ferrers-diagram-Finite-Type : Finite-Type l2
  row-ferrers-diagram-Finite-Type = pr1 D

  type-row-ferrers-diagram-Finite-Type : UU l2
  type-row-ferrers-diagram-Finite-Type =
    type-Finite-Type row-ferrers-diagram-Finite-Type

  is-finite-type-row-ferrers-diagram-Finite-Type :
    is-finite type-row-ferrers-diagram-Finite-Type
  is-finite-type-row-ferrers-diagram-Finite-Type =
    is-finite-type-Finite-Type row-ferrers-diagram-Finite-Type

  dot-ferrers-diagram-Finite-Type :
    type-row-ferrers-diagram-Finite-Type → Finite-Type l3
  dot-ferrers-diagram-Finite-Type = pr1 (pr2 D)

  type-dot-ferrers-diagram-Finite-Type :
    type-row-ferrers-diagram-Finite-Type → UU l3
  type-dot-ferrers-diagram-Finite-Type x =
    type-Finite-Type (dot-ferrers-diagram-Finite-Type x)

  is-finite-type-dot-ferrers-diagram-Finite-Type :
    (x : type-row-ferrers-diagram-Finite-Type) →
    is-finite (type-dot-ferrers-diagram-Finite-Type x)
  is-finite-type-dot-ferrers-diagram-Finite-Type x =
    is-finite-type-Finite-Type (dot-ferrers-diagram-Finite-Type x)

  is-inhabited-dot-ferrers-diagram-Finite-Type :
    (x : type-row-ferrers-diagram-Finite-Type) →
    type-trunc-Prop (type-dot-ferrers-diagram-Finite-Type x)
  is-inhabited-dot-ferrers-diagram-Finite-Type = pr1 (pr2 (pr2 D))

  mere-equiv-ferrers-diagram-Finite-Type :
    mere-equiv
      ( type-Finite-Type A)
      ( Σ ( type-row-ferrers-diagram-Finite-Type)
          ( type-dot-ferrers-diagram-Finite-Type))
  mere-equiv-ferrers-diagram-Finite-Type = pr2 (pr2 (pr2 D))

  ferrers-diagram-ferrers-diagram-Finite-Type :
    ferrers-diagram l2 l3 (type-Finite-Type A)
  pr1 ferrers-diagram-ferrers-diagram-Finite-Type =
    type-row-ferrers-diagram-Finite-Type
  pr1 (pr2 ferrers-diagram-ferrers-diagram-Finite-Type) =
    type-dot-ferrers-diagram-Finite-Type
  pr1 (pr2 (pr2 ferrers-diagram-ferrers-diagram-Finite-Type)) =
    is-inhabited-dot-ferrers-diagram-Finite-Type
  pr2 (pr2 (pr2 ferrers-diagram-ferrers-diagram-Finite-Type)) =
    mere-equiv-ferrers-diagram-Finite-Type
```

### Equivalences of Ferrers diagrams

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (D : ferrers-diagram l2 l3 A)
  where

  equiv-ferrers-diagram :
    {l4 l5 : Level} (E : ferrers-diagram l4 l5 A) → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-ferrers-diagram E =
    Σ ( row-ferrers-diagram D ≃ row-ferrers-diagram E)
      ( λ e →
        (x : row-ferrers-diagram D) →
        dot-ferrers-diagram D x ≃ dot-ferrers-diagram E (map-equiv e x))

  id-equiv-ferrers-diagram : equiv-ferrers-diagram D
  pr1 id-equiv-ferrers-diagram = id-equiv
  pr2 id-equiv-ferrers-diagram x = id-equiv

  equiv-eq-ferrers-diagram :
    (E : ferrers-diagram l2 l3 A) → Id D E → equiv-ferrers-diagram E
  equiv-eq-ferrers-diagram .D refl = id-equiv-ferrers-diagram

  is-torsorial-equiv-ferrers-diagram :
    is-torsorial equiv-ferrers-diagram
  is-torsorial-equiv-ferrers-diagram =
    is-torsorial-Eq-structure
      ( is-torsorial-equiv (row-ferrers-diagram D))
      ( pair (row-ferrers-diagram D) id-equiv)
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv-fam (dot-ferrers-diagram D))
        ( λ Y →
          is-prop-product
            ( is-prop-Π (λ x → is-prop-type-trunc-Prop))
            ( is-prop-mere-equiv A (Σ (row-ferrers-diagram D) Y)))
        ( dot-ferrers-diagram D)
        ( λ x → id-equiv)
        ( pair
          ( is-inhabited-dot-ferrers-diagram D)
          ( mere-equiv-ferrers-diagram D)))

  is-equiv-equiv-eq-ferrers-diagram :
    (E : ferrers-diagram l2 l3 A) → is-equiv (equiv-eq-ferrers-diagram E)
  is-equiv-equiv-eq-ferrers-diagram =
    fundamental-theorem-id
      is-torsorial-equiv-ferrers-diagram
      equiv-eq-ferrers-diagram

  eq-equiv-ferrers-diagram :
    (E : ferrers-diagram l2 l3 A) → equiv-ferrers-diagram E → Id D E
  eq-equiv-ferrers-diagram E =
    map-inv-is-equiv (is-equiv-equiv-eq-ferrers-diagram E)
```

### Equivalences of finite ferrers diagrams of finite types

```agda
module _
  {l1 l2 l3 : Level} (A : Finite-Type l1)
  (D : ferrers-diagram-Finite-Type l2 l3 A)
  where

  equiv-ferrers-diagram-Finite-Type :
    {l4 l5 : Level} → ferrers-diagram-Finite-Type l4 l5 A →
    UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-ferrers-diagram-Finite-Type E =
    equiv-ferrers-diagram
      ( ferrers-diagram-ferrers-diagram-Finite-Type A D)
      ( ferrers-diagram-ferrers-diagram-Finite-Type A E)

  id-equiv-ferrers-diagram-Finite-Type : equiv-ferrers-diagram-Finite-Type D
  id-equiv-ferrers-diagram-Finite-Type =
    id-equiv-ferrers-diagram (ferrers-diagram-ferrers-diagram-Finite-Type A D)

  equiv-eq-ferrers-diagram-Finite-Type :
    (E : ferrers-diagram-Finite-Type l2 l3 A) →
    Id D E → equiv-ferrers-diagram-Finite-Type E
  equiv-eq-ferrers-diagram-Finite-Type .D refl =
    id-equiv-ferrers-diagram-Finite-Type

  is-torsorial-equiv-ferrers-diagram-Finite-Type :
    is-torsorial equiv-ferrers-diagram-Finite-Type
  is-torsorial-equiv-ferrers-diagram-Finite-Type =
    is-torsorial-Eq-structure
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv (type-row-ferrers-diagram-Finite-Type A D))
        ( is-prop-is-finite)
        ( type-row-ferrers-diagram-Finite-Type A D)
        ( id-equiv)
        ( is-finite-type-row-ferrers-diagram-Finite-Type A D))
      ( pair (row-ferrers-diagram-Finite-Type A D) id-equiv)
      ( is-torsorial-Eq-subtype
        ( is-torsorial-Eq-Π
          ( λ x →
            is-torsorial-Eq-subtype
              ( is-torsorial-equiv (type-dot-ferrers-diagram-Finite-Type A D x))
              ( is-prop-is-finite)
              ( type-dot-ferrers-diagram-Finite-Type A D x)
              ( id-equiv)
              ( is-finite-type-dot-ferrers-diagram-Finite-Type A D x)))
        ( λ x →
          is-prop-product
            ( is-prop-Π (λ x → is-prop-type-trunc-Prop))
            ( is-prop-mere-equiv (type-Finite-Type A) _))
        ( dot-ferrers-diagram-Finite-Type A D)
        ( λ x → id-equiv)
        ( pair
          ( is-inhabited-dot-ferrers-diagram-Finite-Type A D)
          ( mere-equiv-ferrers-diagram-Finite-Type A D)))

  is-equiv-equiv-eq-ferrers-diagram-Finite-Type :
    (E : ferrers-diagram-Finite-Type l2 l3 A) →
    is-equiv (equiv-eq-ferrers-diagram-Finite-Type E)
  is-equiv-equiv-eq-ferrers-diagram-Finite-Type =
    fundamental-theorem-id
      is-torsorial-equiv-ferrers-diagram-Finite-Type
      equiv-eq-ferrers-diagram-Finite-Type

  eq-equiv-ferrers-diagram-Finite-Type :
    (E : ferrers-diagram-Finite-Type l2 l3 A) →
    equiv-ferrers-diagram-Finite-Type E → Id D E
  eq-equiv-ferrers-diagram-Finite-Type E =
    map-inv-is-equiv (is-equiv-equiv-eq-ferrers-diagram-Finite-Type E)
```

## Properties

### The type of Ferrers diagrams of any finite type is π-finite

This remains to be shown.
[#746](https://github.com/UniMath/agda-unimath/issues/746)

## See also

- Integer partitions in
  [`elementary-number-theory.integer-partitions`](elementary-number-theory.integer-partitions.md)
