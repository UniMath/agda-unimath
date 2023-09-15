# Concrete groups

```agda
module group-theory.concrete-groups where
```

<details><summary>Imports</summary>

```agda
open import foundation.0-connected-types
open import foundation.1-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import group-theory.groups

open import higher-group-theory.higher-groups

open import structured-types.pointed-types
```

</details>

## Idea

A **concrete group** is a [pointed](structured-types.pointed-types.md)
[connected](foundation.0-connected-types.md)
[1-type](foundation-core.1-types.md).

## Definition

```agda
Concrete-Group : (l : Level) → UU (lsuc l)
Concrete-Group l = Σ (∞-Group l) (λ G → is-set (type-∞-Group G))

module _
  {l : Level} (G : Concrete-Group l)
  where

  ∞-group-Concrete-Group : ∞-Group l
  ∞-group-Concrete-Group = pr1 G

  classifying-pointed-type-Concrete-Group : Pointed-Type l
  classifying-pointed-type-Concrete-Group =
    classifying-pointed-type-∞-Group ∞-group-Concrete-Group

  classifying-type-Concrete-Group : UU l
  classifying-type-Concrete-Group =
    classifying-type-∞-Group ∞-group-Concrete-Group

  shape-Concrete-Group : classifying-type-Concrete-Group
  shape-Concrete-Group =
    shape-∞-Group ∞-group-Concrete-Group

  is-0-connected-classifying-type-Concrete-Group :
    is-0-connected classifying-type-Concrete-Group
  is-0-connected-classifying-type-Concrete-Group =
    is-0-connected-classifying-type-∞-Group ∞-group-Concrete-Group

  mere-eq-classifying-type-Concrete-Group :
    (X Y : classifying-type-Concrete-Group) → mere-eq X Y
  mere-eq-classifying-type-Concrete-Group =
    mere-eq-classifying-type-∞-Group ∞-group-Concrete-Group

  elim-prop-classifying-type-Concrete-Group :
    {l2 : Level} (P : classifying-type-Concrete-Group → Prop l2) →
    type-Prop (P shape-Concrete-Group) →
    ((X : classifying-type-Concrete-Group) → type-Prop (P X))
  elim-prop-classifying-type-Concrete-Group =
    elim-prop-classifying-type-∞-Group ∞-group-Concrete-Group

  type-Concrete-Group : UU l
  type-Concrete-Group = type-∞-Group ∞-group-Concrete-Group

  is-set-type-Concrete-Group : is-set type-Concrete-Group
  is-set-type-Concrete-Group = pr2 G

  set-Concrete-Group : Set l
  pr1 set-Concrete-Group = type-Concrete-Group
  pr2 set-Concrete-Group = is-set-type-Concrete-Group

  abstract
    is-1-type-classifying-type-Concrete-Group :
      is-trunc one-𝕋 classifying-type-Concrete-Group
    is-1-type-classifying-type-Concrete-Group X Y =
      apply-universal-property-trunc-Prop
        ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group X)
        ( is-set-Prop (X ＝ Y))
        ( λ
          { refl →
            apply-universal-property-trunc-Prop
              ( mere-eq-classifying-type-Concrete-Group shape-Concrete-Group Y)
              ( is-set-Prop (shape-Concrete-Group ＝ Y))
              ( λ { refl → is-set-type-Concrete-Group})})

  classifying-1-type-Concrete-Group : Truncated-Type l one-𝕋
  pr1 classifying-1-type-Concrete-Group =
    classifying-type-Concrete-Group
  pr2 classifying-1-type-Concrete-Group =
    is-1-type-classifying-type-Concrete-Group

  Id-BG-Set :
    (X Y : classifying-type-Concrete-Group) → Set l
  Id-BG-Set X Y = Id-Set classifying-1-type-Concrete-Group X Y

  unit-Concrete-Group : type-Concrete-Group
  unit-Concrete-Group = unit-∞-Group ∞-group-Concrete-Group

  mul-Concrete-Group : (x y : type-Concrete-Group) → type-Concrete-Group
  mul-Concrete-Group = mul-∞-Group ∞-group-Concrete-Group

  mul-Concrete-Group' : (x y : type-Concrete-Group) → type-Concrete-Group
  mul-Concrete-Group' x y = mul-Concrete-Group y x

  associative-mul-Concrete-Group :
    (x y z : type-Concrete-Group) →
    ( mul-Concrete-Group (mul-Concrete-Group x y) z) ＝
    ( mul-Concrete-Group x (mul-Concrete-Group y z))
  associative-mul-Concrete-Group =
    associative-mul-∞-Group ∞-group-Concrete-Group

  left-unit-law-mul-Concrete-Group :
    (x : type-Concrete-Group) → mul-Concrete-Group unit-Concrete-Group x ＝ x
  left-unit-law-mul-Concrete-Group =
    left-unit-law-mul-∞-Group ∞-group-Concrete-Group

  right-unit-law-mul-Concrete-Group :
    (y : type-Concrete-Group) → mul-Concrete-Group y unit-Concrete-Group ＝ y
  right-unit-law-mul-Concrete-Group =
    right-unit-law-mul-∞-Group ∞-group-Concrete-Group

  coherence-unit-laws-mul-Concrete-Group :
    left-unit-law-mul-Concrete-Group unit-Concrete-Group ＝
    right-unit-law-mul-Concrete-Group unit-Concrete-Group
  coherence-unit-laws-mul-Concrete-Group =
    coherence-unit-laws-mul-∞-Group ∞-group-Concrete-Group

  inv-Concrete-Group : type-Concrete-Group → type-Concrete-Group
  inv-Concrete-Group = inv-∞-Group ∞-group-Concrete-Group

  left-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    mul-Concrete-Group (inv-Concrete-Group x) x ＝ unit-Concrete-Group
  left-inverse-law-mul-Concrete-Group =
    left-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  right-inverse-law-mul-Concrete-Group :
    (x : type-Concrete-Group) →
    mul-Concrete-Group x (inv-Concrete-Group x) ＝ unit-Concrete-Group
  right-inverse-law-mul-Concrete-Group =
    right-inverse-law-mul-∞-Group ∞-group-Concrete-Group

  abstract-group-Concrete-Group : Group l
  pr1 (pr1 abstract-group-Concrete-Group) = set-Concrete-Group
  pr1 (pr2 (pr1 abstract-group-Concrete-Group)) = mul-Concrete-Group
  pr2 (pr2 (pr1 abstract-group-Concrete-Group)) = associative-mul-Concrete-Group
  pr1 (pr1 (pr2 abstract-group-Concrete-Group)) = unit-Concrete-Group
  pr1 (pr2 (pr1 (pr2 abstract-group-Concrete-Group))) =
    left-unit-law-mul-Concrete-Group
  pr2 (pr2 (pr1 (pr2 abstract-group-Concrete-Group))) =
    right-unit-law-mul-Concrete-Group
  pr1 (pr2 (pr2 abstract-group-Concrete-Group)) =
    inv-Concrete-Group
  pr1 (pr2 (pr2 (pr2 abstract-group-Concrete-Group))) =
    left-inverse-law-mul-Concrete-Group
  pr2 (pr2 (pr2 (pr2 abstract-group-Concrete-Group))) =
    right-inverse-law-mul-Concrete-Group

  op-abstract-group-Concrete-Group : Group l
  pr1 (pr1 op-abstract-group-Concrete-Group) = set-Concrete-Group
  pr1 (pr2 (pr1 op-abstract-group-Concrete-Group)) = mul-Concrete-Group'
  pr2 (pr2 (pr1 op-abstract-group-Concrete-Group)) x y z =
    inv (associative-mul-Concrete-Group z y x)
  pr1 (pr1 (pr2 op-abstract-group-Concrete-Group)) = unit-Concrete-Group
  pr1 (pr2 (pr1 (pr2 op-abstract-group-Concrete-Group))) =
    right-unit-law-mul-Concrete-Group
  pr2 (pr2 (pr1 (pr2 op-abstract-group-Concrete-Group))) =
    left-unit-law-mul-Concrete-Group
  pr1 (pr2 (pr2 op-abstract-group-Concrete-Group)) = inv-Concrete-Group
  pr1 (pr2 (pr2 (pr2 op-abstract-group-Concrete-Group))) =
    right-inverse-law-mul-Concrete-Group
  pr2 (pr2 (pr2 (pr2 op-abstract-group-Concrete-Group))) =
    left-inverse-law-mul-Concrete-Group
```
