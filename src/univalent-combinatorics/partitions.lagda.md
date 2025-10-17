# Partitions of finite types

```agda
module univalent-combinatorics.partitions where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.equality-cartesian-product-types
open import foundation.equivalence-extensionality
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

A **partition** of a [finite type](univalent-combinatorics.finite-types.md) `X`
can be defined in several equivalent ways:

- A partition is a [subset](foundation.subtypes.md) `P` of the
  [powerset](foundation.powersets.md) of `X` such that each `U ⊆ X` in `P` is
  [inhabited](foundation.inhabited-types.md) and each element `x : X` is in
  exactly one subset `U ⊆ X` in `P`.
- A partition is an
  [equivalence relation](foundation-core.equivalence-relations.md) on `X`
- A partition is a decomposition of `X` into a type of the form `Σ A B` where
  `A` is finite and `B` is a family of inhabited finite types, i.e., it consists
  of such `A` and `B` and an [equivalence](foundation-core.equivalences.md)
  `X ≃ Σ A B`.

Note that the last description is subtly different from the notion of
[unlabeled partition](univalent-combinatorics.ferrers-diagrams.md) (i.e.,
Ferrers diagram), because it only uses
[mere equivalences](foundation.mere-equivalences.md).

## Definition

### Partitions

```agda
partition-Finite-Type :
  {l1 : Level} (l2 l3 : Level) → Finite-Type l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
partition-Finite-Type l2 l3 X =
  Σ ( Finite-Type l2)
    ( λ Y →
      Σ ( type-Finite-Type Y → Finite-Type l3)
        ( λ Z →
          ( (y : type-Finite-Type Y) →
            type-trunc-Prop (type-Finite-Type (Z y))) ×
          ( equiv-Finite-Type X (Σ-Finite-Type Y Z))))

module _
  {l1 l2 l3 : Level} (X : Finite-Type l1) (P : partition-Finite-Type l2 l3 X)
  where

  finite-indexing-type-partition-Finite-Type : Finite-Type l2
  finite-indexing-type-partition-Finite-Type = pr1 P

  indexing-type-partition-Finite-Type : UU l2
  indexing-type-partition-Finite-Type =
    type-Finite-Type finite-indexing-type-partition-Finite-Type

  is-finite-indexing-type-partition-Finite-Type :
    is-finite indexing-type-partition-Finite-Type
  is-finite-indexing-type-partition-Finite-Type =
    is-finite-type-Finite-Type finite-indexing-type-partition-Finite-Type

  number-of-elements-indexing-type-partition-Finite-Type : ℕ
  number-of-elements-indexing-type-partition-Finite-Type =
    number-of-elements-is-finite is-finite-indexing-type-partition-Finite-Type

  finite-block-partition-Finite-Type :
    indexing-type-partition-Finite-Type → Finite-Type l3
  finite-block-partition-Finite-Type = pr1 (pr2 P)

  block-partition-Finite-Type : indexing-type-partition-Finite-Type → UU l3
  block-partition-Finite-Type i =
    type-Finite-Type (finite-block-partition-Finite-Type i)

  is-finite-block-partition-Finite-Type :
    (i : indexing-type-partition-Finite-Type) →
    is-finite (block-partition-Finite-Type i)
  is-finite-block-partition-Finite-Type i =
    is-finite-type-Finite-Type (finite-block-partition-Finite-Type i)

  number-of-elements-block-partition-Finite-Type :
    indexing-type-partition-Finite-Type → ℕ
  number-of-elements-block-partition-Finite-Type i =
    number-of-elements-is-finite (is-finite-block-partition-Finite-Type i)

  is-inhabited-block-partition-Finite-Type :
    (i : indexing-type-partition-Finite-Type) →
    type-trunc-Prop (block-partition-Finite-Type i)
  is-inhabited-block-partition-Finite-Type = pr1 (pr2 (pr2 P))

  conversion-partition-Finite-Type :
    equiv-Finite-Type X
      ( Σ-Finite-Type
          finite-indexing-type-partition-Finite-Type
          finite-block-partition-Finite-Type)
  conversion-partition-Finite-Type = pr2 (pr2 (pr2 P))

  map-conversion-partition-Finite-Type :
    type-Finite-Type X →
    Σ indexing-type-partition-Finite-Type block-partition-Finite-Type
  map-conversion-partition-Finite-Type =
    map-equiv conversion-partition-Finite-Type

  rel-partition-prop-Finite-Type :
    type-Finite-Type X → type-Finite-Type X → Prop l2
  rel-partition-prop-Finite-Type x y =
    Id-Prop
      ( set-Finite-Type finite-indexing-type-partition-Finite-Type)
      ( pr1 (map-conversion-partition-Finite-Type x))
      ( pr1 (map-conversion-partition-Finite-Type y))

  rel-partition-Finite-Type : type-Finite-Type X → type-Finite-Type X → UU l2
  rel-partition-Finite-Type x y = type-Prop (rel-partition-prop-Finite-Type x y)

  is-prop-rel-partition-Finite-Type :
    (x y : type-Finite-Type X) → is-prop (rel-partition-Finite-Type x y)
  is-prop-rel-partition-Finite-Type x y =
    is-prop-type-Prop (rel-partition-prop-Finite-Type x y)

  refl-rel-partition-Finite-Type : is-reflexive rel-partition-Finite-Type
  refl-rel-partition-Finite-Type x = refl

  symmetric-rel-partition-Finite-Type : is-symmetric rel-partition-Finite-Type
  symmetric-rel-partition-Finite-Type x y = inv

  transitive-rel-partition-Finite-Type : is-transitive rel-partition-Finite-Type
  transitive-rel-partition-Finite-Type x y z r s = s ∙ r

  equivalence-relation-partition-Finite-Type :
    equivalence-relation l2 (type-Finite-Type X)
  pr1 equivalence-relation-partition-Finite-Type =
    rel-partition-prop-Finite-Type
  pr1 (pr2 equivalence-relation-partition-Finite-Type) =
    refl-rel-partition-Finite-Type
  pr1 (pr2 (pr2 equivalence-relation-partition-Finite-Type)) =
    symmetric-rel-partition-Finite-Type
  pr2 (pr2 (pr2 equivalence-relation-partition-Finite-Type)) =
    transitive-rel-partition-Finite-Type
```

### Equivalences of partitions

```agda
equiv-partition-Finite-Type :
  {l1 l2 l3 l4 l5 : Level} (X : Finite-Type l1) →
  partition-Finite-Type l2 l3 X →
  partition-Finite-Type l4 l5 X →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
equiv-partition-Finite-Type X P Q =
  Σ ( indexing-type-partition-Finite-Type X P ≃
      indexing-type-partition-Finite-Type X Q)
    ( λ e →
      Σ ( (i : indexing-type-partition-Finite-Type X P) →
          block-partition-Finite-Type X P i ≃
          block-partition-Finite-Type X Q (map-equiv e i))
        ( λ f →
          htpy-equiv
            ( ( equiv-Σ (block-partition-Finite-Type X Q) e f) ∘e
              ( conversion-partition-Finite-Type X P))
            ( conversion-partition-Finite-Type X Q)))

id-equiv-partition-Finite-Type :
  {l1 l2 l3 : Level} (X : Finite-Type l1)
  (P : partition-Finite-Type l2 l3 X) → equiv-partition-Finite-Type X P P
pr1 (id-equiv-partition-Finite-Type X P) = id-equiv
pr1 (pr2 (id-equiv-partition-Finite-Type X P)) i = id-equiv
pr2 (pr2 (id-equiv-partition-Finite-Type X P)) = refl-htpy

extensionality-partition-Finite-Type :
  {l1 l2 l3 : Level} (X : Finite-Type l1)
  (P Q : partition-Finite-Type l2 l3 X) →
  (P ＝ Q) ≃ equiv-partition-Finite-Type X P Q
extensionality-partition-Finite-Type X P =
  extensionality-Σ
    ( λ {Y} Zf e →
      Σ ( (i : indexing-type-partition-Finite-Type X P) →
          block-partition-Finite-Type X P i ≃
          type-Finite-Type (pr1 Zf (map-equiv e i)))
        ( λ f →
          htpy-equiv
            ( equiv-Σ (type-Finite-Type ∘ pr1 Zf) e f ∘e
              conversion-partition-Finite-Type X P)
            ( pr2 (pr2 Zf))))
    ( id-equiv)
    ( pair (λ i → id-equiv) refl-htpy)
    ( extensionality-Finite-Type
      ( finite-indexing-type-partition-Finite-Type X P))
    ( extensionality-Σ
      ( λ {Z} f α →
        htpy-equiv
          ( equiv-Σ (type-Finite-Type ∘ Z) id-equiv α ∘e
            conversion-partition-Finite-Type X P)
          ( pr2 f))
      ( λ i → id-equiv)
      ( refl-htpy)
      ( extensionality-fam-Finite-Type
        ( finite-block-partition-Finite-Type X P))
      ( λ α →
        ( ( extensionality-equiv
            ( conversion-partition-Finite-Type X P)
            ( pr2 α)) ∘e
          ( left-unit-law-product-is-contr
            ( is-prop-Π
              ( λ _ → is-prop-type-trunc-Prop)
              ( is-inhabited-block-partition-Finite-Type X P)
              ( pr1 α)))) ∘e
        ( equiv-pair-eq (pr2 (pr2 P)) α)))
```

## Properties

### The type of finite partitions of a finite type `X` is equivalent to the type of decidable partitions of `X` in the usual sense

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The type of finite partitions of a finite type `X` is equivalent to the type of equivalence relations on `X`

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The type of finite partitions of a finite type is finite

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The number of elements of the type of finite partitions of a finite type is a Stirling number of the second kind

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)

### The type of finite partitions of a contractible type is contractible

This remains to be shown.
[#747](https://github.com/UniMath/agda-unimath/issues/747)
