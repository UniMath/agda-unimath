# Higher groups

```agda
module higher-group-theory.higher-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.full-subtypes
open import foundation.identity-types
open import foundation.images
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import structured-types.h-spaces
open import structured-types.pointed-types

open import synthetic-homotopy-theory.loop-spaces
```

</details>

## Idea

An **∞-group** is just a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md) type. Its underlying type is its
[loop space](synthetic-homotopy-theory.loop-spaces.md), and the classifying type
is the pointed connected type itself.

## Definition

```agda
∞-Group : (l : Level) → UU (lsuc l)
∞-Group l = Σ (Pointed-Type l) (λ X → is-0-connected (type-Pointed-Type X))

module _
  {l : Level} (G : ∞-Group l)
  where

  classifying-pointed-type-∞-Group : Pointed-Type l
  classifying-pointed-type-∞-Group = pr1 G

  classifying-type-∞-Group : UU l
  classifying-type-∞-Group =
    type-Pointed-Type classifying-pointed-type-∞-Group

  shape-∞-Group : classifying-type-∞-Group
  shape-∞-Group =
    point-Pointed-Type classifying-pointed-type-∞-Group

  point-∞-Group : unit → classifying-type-∞-Group
  point-∞-Group = point shape-∞-Group

  abstract
    is-0-connected-classifying-type-∞-Group :
      is-0-connected classifying-type-∞-Group
    is-0-connected-classifying-type-∞-Group = pr2 G

  abstract
    mere-eq-classifying-type-∞-Group :
      (X Y : classifying-type-∞-Group) → mere-eq X Y
    mere-eq-classifying-type-∞-Group =
      mere-eq-is-0-connected
        is-0-connected-classifying-type-∞-Group

  abstract
    is-full-subtype-im-point-∞-Group :
      is-full-subtype (subtype-im point-∞-Group)
    is-full-subtype-im-point-∞-Group x =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-∞-Group shape-∞-Group x)
        ( subtype-im point-∞-Group x)
        ( λ where refl → unit-trunc-Prop (star , refl))

  compute-im-point-∞-Group :
    im point-∞-Group ≃ classifying-type-∞-Group
  compute-im-point-∞-Group =
    equiv-inclusion-is-full-subtype
      ( subtype-im point-∞-Group)
      ( is-full-subtype-im-point-∞-Group)

  abstract
    elim-prop-classifying-type-∞-Group :
      {l2 : Level} (P : classifying-type-∞-Group → Prop l2) →
      type-Prop (P shape-∞-Group) →
      ((X : classifying-type-∞-Group) → type-Prop (P X))
    elim-prop-classifying-type-∞-Group =
      apply-dependent-universal-property-is-0-connected
        shape-∞-Group
        is-0-connected-classifying-type-∞-Group

  h-space-∞-Group : H-Space l
  h-space-∞-Group = Ω-H-Space classifying-pointed-type-∞-Group

  pointed-type-∞-Group : Pointed-Type l
  pointed-type-∞-Group = Ω classifying-pointed-type-∞-Group

  type-∞-Group : UU l
  type-∞-Group = type-Pointed-Type pointed-type-∞-Group

  unit-∞-Group : type-∞-Group
  unit-∞-Group = point-Pointed-Type pointed-type-∞-Group

  mul-∞-Group : (x y : type-∞-Group) → type-∞-Group
  mul-∞-Group = mul-Ω classifying-pointed-type-∞-Group

  associative-mul-∞-Group :
    (x y z : type-∞-Group) →
    Id
      ( mul-∞-Group (mul-∞-Group x y) z)
      ( mul-∞-Group x (mul-∞-Group y z))
  associative-mul-∞-Group = associative-mul-Ω classifying-pointed-type-∞-Group

  left-unit-law-mul-∞-Group :
    (x : type-∞-Group) → mul-∞-Group unit-∞-Group x ＝ x
  left-unit-law-mul-∞-Group =
    left-unit-law-mul-Ω classifying-pointed-type-∞-Group

  right-unit-law-mul-∞-Group :
    (y : type-∞-Group) → mul-∞-Group y unit-∞-Group ＝ y
  right-unit-law-mul-∞-Group =
    right-unit-law-mul-Ω classifying-pointed-type-∞-Group

  coherence-unit-laws-mul-∞-Group :
    left-unit-law-mul-∞-Group unit-∞-Group ＝
    right-unit-law-mul-∞-Group unit-∞-Group
  coherence-unit-laws-mul-∞-Group =
    coherence-unit-laws-mul-Ω classifying-pointed-type-∞-Group

  inv-∞-Group : type-∞-Group → type-∞-Group
  inv-∞-Group = inv-Ω classifying-pointed-type-∞-Group

  left-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group (inv-∞-Group x) x) unit-∞-Group
  left-inverse-law-mul-∞-Group =
    left-inverse-law-mul-Ω classifying-pointed-type-∞-Group

  right-inverse-law-mul-∞-Group :
    (x : type-∞-Group) → Id (mul-∞-Group x (inv-∞-Group x)) unit-∞-Group
  right-inverse-law-mul-∞-Group =
    right-inverse-law-mul-Ω classifying-pointed-type-∞-Group
```
