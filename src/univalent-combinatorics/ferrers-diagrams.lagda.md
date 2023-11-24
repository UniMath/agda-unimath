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
of the [cardinality](set-theory.cardinalities.md) of `A`.

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
ferrers-diagram-𝔽 :
  {l1 : Level} (l2 l3 : Level) (A : 𝔽 l1) → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
ferrers-diagram-𝔽 {l} l2 l3 A =
  Σ ( 𝔽 l2)
    ( λ X →
      Σ ( type-𝔽 X → 𝔽 l3)
        ( λ Y →
          ((x : type-𝔽 X) → type-trunc-Prop (type-𝔽 (Y x))) ×
          mere-equiv (type-𝔽 A) (Σ (type-𝔽 X) (λ x → type-𝔽 (Y x)))))

module _
  {l1 l2 l3 : Level} (A : 𝔽 l1) (D : ferrers-diagram-𝔽 l2 l3 A)
  where

  row-ferrers-diagram-𝔽 : 𝔽 l2
  row-ferrers-diagram-𝔽 = pr1 D

  type-row-ferrers-diagram-𝔽 : UU l2
  type-row-ferrers-diagram-𝔽 = type-𝔽 row-ferrers-diagram-𝔽

  is-finite-type-row-ferrers-diagram-𝔽 : is-finite type-row-ferrers-diagram-𝔽
  is-finite-type-row-ferrers-diagram-𝔽 =
    is-finite-type-𝔽 row-ferrers-diagram-𝔽

  dot-ferrers-diagram-𝔽 : type-row-ferrers-diagram-𝔽 → 𝔽 l3
  dot-ferrers-diagram-𝔽 = pr1 (pr2 D)

  type-dot-ferrers-diagram-𝔽 : type-row-ferrers-diagram-𝔽 → UU l3
  type-dot-ferrers-diagram-𝔽 x = type-𝔽 (dot-ferrers-diagram-𝔽 x)

  is-finite-type-dot-ferrers-diagram-𝔽 :
    (x : type-row-ferrers-diagram-𝔽) → is-finite (type-dot-ferrers-diagram-𝔽 x)
  is-finite-type-dot-ferrers-diagram-𝔽 x =
    is-finite-type-𝔽 (dot-ferrers-diagram-𝔽 x)

  is-inhabited-dot-ferrers-diagram-𝔽 :
    (x : type-row-ferrers-diagram-𝔽) →
    type-trunc-Prop (type-dot-ferrers-diagram-𝔽 x)
  is-inhabited-dot-ferrers-diagram-𝔽 = pr1 (pr2 (pr2 D))

  mere-equiv-ferrers-diagram-𝔽 :
    mere-equiv
      ( type-𝔽 A)
      ( Σ (type-row-ferrers-diagram-𝔽) (type-dot-ferrers-diagram-𝔽))
  mere-equiv-ferrers-diagram-𝔽 = pr2 (pr2 (pr2 D))

  ferrers-diagram-ferrers-diagram-𝔽 : ferrers-diagram l2 l3 (type-𝔽 A)
  pr1 ferrers-diagram-ferrers-diagram-𝔽 = type-row-ferrers-diagram-𝔽
  pr1 (pr2 ferrers-diagram-ferrers-diagram-𝔽) = type-dot-ferrers-diagram-𝔽
  pr1 (pr2 (pr2 ferrers-diagram-ferrers-diagram-𝔽)) =
    is-inhabited-dot-ferrers-diagram-𝔽
  pr2 (pr2 (pr2 ferrers-diagram-ferrers-diagram-𝔽)) =
    mere-equiv-ferrers-diagram-𝔽
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
      ( λ X Y e →
        (x : row-ferrers-diagram D) →
        dot-ferrers-diagram D x ≃ pr1 Y (map-equiv e x))
      ( is-torsorial-equiv (row-ferrers-diagram D))
      ( pair (row-ferrers-diagram D) id-equiv)
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv-fam (dot-ferrers-diagram D))
        ( λ Y →
          is-prop-prod
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
  {l1 l2 l3 : Level} (A : 𝔽 l1) (D : ferrers-diagram-𝔽 l2 l3 A)
  where

  equiv-ferrers-diagram-𝔽 :
    {l4 l5 : Level} → ferrers-diagram-𝔽 l4 l5 A → UU (l2 ⊔ l3 ⊔ l4 ⊔ l5)
  equiv-ferrers-diagram-𝔽 E =
    equiv-ferrers-diagram
      ( ferrers-diagram-ferrers-diagram-𝔽 A D)
      ( ferrers-diagram-ferrers-diagram-𝔽 A E)

  id-equiv-ferrers-diagram-𝔽 : equiv-ferrers-diagram-𝔽 D
  id-equiv-ferrers-diagram-𝔽 =
    id-equiv-ferrers-diagram (ferrers-diagram-ferrers-diagram-𝔽 A D)

  equiv-eq-ferrers-diagram-𝔽 :
    (E : ferrers-diagram-𝔽 l2 l3 A) → Id D E → equiv-ferrers-diagram-𝔽 E
  equiv-eq-ferrers-diagram-𝔽 .D refl = id-equiv-ferrers-diagram-𝔽

  is-torsorial-equiv-ferrers-diagram-𝔽 :
    is-torsorial equiv-ferrers-diagram-𝔽
  is-torsorial-equiv-ferrers-diagram-𝔽 =
    is-torsorial-Eq-structure
      ( λ X Y e →
        (x : type-row-ferrers-diagram-𝔽 A D) →
        type-dot-ferrers-diagram-𝔽 A D x ≃ type-𝔽 (pr1 Y (map-equiv e x)))
      ( is-torsorial-Eq-subtype
        ( is-torsorial-equiv (type-row-ferrers-diagram-𝔽 A D))
        ( is-prop-is-finite)
        ( type-row-ferrers-diagram-𝔽 A D)
        ( id-equiv)
        ( is-finite-type-row-ferrers-diagram-𝔽 A D))
      ( pair (row-ferrers-diagram-𝔽 A D) id-equiv)
      ( is-torsorial-Eq-subtype
        ( is-torsorial-Eq-Π
          ( λ x Y → type-dot-ferrers-diagram-𝔽 A D x ≃ type-𝔽 Y)
          ( λ x →
            is-torsorial-Eq-subtype
              ( is-torsorial-equiv (type-dot-ferrers-diagram-𝔽 A D x))
              ( is-prop-is-finite)
              ( type-dot-ferrers-diagram-𝔽 A D x)
              ( id-equiv)
              ( is-finite-type-dot-ferrers-diagram-𝔽 A D x)))
        ( λ x →
          is-prop-prod
            ( is-prop-Π (λ x → is-prop-type-trunc-Prop))
            ( is-prop-mere-equiv (type-𝔽 A) _))
        ( dot-ferrers-diagram-𝔽 A D)
        ( λ x → id-equiv)
        ( pair
          ( is-inhabited-dot-ferrers-diagram-𝔽 A D)
          ( mere-equiv-ferrers-diagram-𝔽 A D)))

  is-equiv-equiv-eq-ferrers-diagram-𝔽 :
    (E : ferrers-diagram-𝔽 l2 l3 A) → is-equiv (equiv-eq-ferrers-diagram-𝔽 E)
  is-equiv-equiv-eq-ferrers-diagram-𝔽 =
    fundamental-theorem-id
      is-torsorial-equiv-ferrers-diagram-𝔽
      equiv-eq-ferrers-diagram-𝔽

  eq-equiv-ferrers-diagram-𝔽 :
    (E : ferrers-diagram-𝔽 l2 l3 A) → equiv-ferrers-diagram-𝔽 E → Id D E
  eq-equiv-ferrers-diagram-𝔽 E =
    map-inv-is-equiv (is-equiv-equiv-eq-ferrers-diagram-𝔽 E)
```

## Properties

### The type of Ferrers diagrams of any finite type is π-finite

This remains to be shown.
[#746](https://github.com/UniMath/agda-unimath/issues/746)

## See also

- Integer partitions in
  [`elementary-number-theory.integer-partitions`](elementary-number-theory.integer-partitions.md)
