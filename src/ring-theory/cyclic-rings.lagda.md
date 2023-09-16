# Cyclic rings

```agda
module ring-theory.cyclic-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.cyclic-groups
open import group-theory.generating-elements-groups
open import group-theory.groups

open import ring-theory.integer-multiples-of-elements-rings
open import ring-theory.rings
```

</details>

## Idea

A [ring](ring-theory.rings.md) is said to be **cyclic** if its underlying additive [group](group-theory.groups.md) is a [cyclic group](group-theory.cyclic-groups.md).

Since rings in the agda-unimath library are assumed to be unital by default, it follows that cyclic rings come equipped with a [generating element](group-theory.generating-elements-groups.md). Indeed, the unit element is a generating element of any cyclic ring.

## Definitions

### The predicate of being a cyclic ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-cyclic-prop-Ring : Prop l
  is-cyclic-prop-Ring = is-cyclic-prop-Group (group-Ring R)

  is-cyclic-Ring : UU l
  is-cyclic-Ring = is-cyclic-Group (group-Ring R)

  is-prop-is-cyclic-Ring : is-prop is-cyclic-Ring
  is-prop-is-cyclic-Ring = is-prop-is-cyclic-Group (group-Ring R)
```

### Cyclic rings

```agda
Cyclic-Ring : (l : Level) → UU (lsuc l)
Cyclic-Ring l = Σ (Ring l) is-cyclic-Ring

module _
  {l : Level} (R : Cyclic-Ring l)
  where

  ring-Cyclic-Ring : Ring l
  ring-Cyclic-Ring = pr1 R

  ab-Cyclic-Ring : Ab l
  ab-Cyclic-Ring = ab-Ring ring-Cyclic-Ring

  group-Cyclic-Ring : Group l
  group-Cyclic-Ring = group-Ring ring-Cyclic-Ring

  is-cyclic-Cyclic-Ring : is-cyclic-Ring ring-Cyclic-Ring
  is-cyclic-Cyclic-Ring = pr2 R

  cyclic-group-Cyclic-Ring : Cyclic-Group l
  pr1 cyclic-group-Cyclic-Ring = group-Cyclic-Ring
  pr2 cyclic-group-Cyclic-Ring = is-cyclic-Cyclic-Ring

  type-Cyclic-Ring : UU l
  type-Cyclic-Ring = type-Ring ring-Cyclic-Ring

  set-Cyclic-Ring : Set l
  set-Cyclic-Ring = set-Ring ring-Cyclic-Ring

  zero-Cyclic-Ring : type-Cyclic-Ring
  zero-Cyclic-Ring = zero-Ring ring-Cyclic-Ring

  one-Cyclic-Ring : type-Cyclic-Ring
  one-Cyclic-Ring = one-Ring ring-Cyclic-Ring

  add-Cyclic-Ring : (x y : type-Cyclic-Ring) → type-Cyclic-Ring
  add-Cyclic-Ring = add-Ring ring-Cyclic-Ring

  neg-Cyclic-Ring : type-Cyclic-Ring → type-Cyclic-Ring
  neg-Cyclic-Ring = neg-Ring ring-Cyclic-Ring

  mul-Cyclic-Ring : (x y : type-Cyclic-Ring) → type-Cyclic-Ring
  mul-Cyclic-Ring = mul-Ring ring-Cyclic-Ring

  integer-multiple-Cyclic-Ring : ℤ → type-Cyclic-Ring → type-Cyclic-Ring
  integer-multiple-Cyclic-Ring = integer-multiple-Ring ring-Cyclic-Ring

  left-unit-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring zero-Cyclic-Ring x ＝ x
  left-unit-law-add-Cyclic-Ring =
    left-unit-law-add-Ring ring-Cyclic-Ring

  right-unit-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring x zero-Cyclic-Ring ＝ x
  right-unit-law-add-Cyclic-Ring =
    right-unit-law-add-Ring ring-Cyclic-Ring

  associative-add-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    add-Cyclic-Ring (add-Cyclic-Ring x y) z ＝
    add-Cyclic-Ring x (add-Cyclic-Ring y z)
  associative-add-Cyclic-Ring =
    associative-add-Ring ring-Cyclic-Ring

  left-inverse-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring (neg-Cyclic-Ring x) x ＝ zero-Cyclic-Ring
  left-inverse-law-add-Cyclic-Ring =
    left-inverse-law-add-Ring ring-Cyclic-Ring

  right-inverse-law-add-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    add-Cyclic-Ring x (neg-Cyclic-Ring x) ＝ zero-Cyclic-Ring
  right-inverse-law-add-Cyclic-Ring =
    right-inverse-law-add-Ring ring-Cyclic-Ring

  left-unit-law-mul-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    mul-Cyclic-Ring one-Cyclic-Ring x ＝ x
  left-unit-law-mul-Cyclic-Ring =
    left-unit-law-mul-Ring ring-Cyclic-Ring

  right-unit-law-mul-Cyclic-Ring :
    (x : type-Cyclic-Ring) →
    mul-Cyclic-Ring x one-Cyclic-Ring ＝ x
  right-unit-law-mul-Cyclic-Ring =
    right-unit-law-mul-Ring ring-Cyclic-Ring

  associative-mul-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    mul-Cyclic-Ring (mul-Cyclic-Ring x y) z ＝
    mul-Cyclic-Ring x (mul-Cyclic-Ring y z)
  associative-mul-Cyclic-Ring =
    associative-mul-Ring ring-Cyclic-Ring

  left-distributive-mul-add-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    mul-Cyclic-Ring x (add-Cyclic-Ring y z) ＝
    add-Cyclic-Ring (mul-Cyclic-Ring x y) (mul-Cyclic-Ring x z)
  left-distributive-mul-add-Cyclic-Ring =
    left-distributive-mul-add-Ring ring-Cyclic-Ring

  right-distributive-mul-add-Cyclic-Ring :
    (x y z : type-Cyclic-Ring) →
    mul-Cyclic-Ring (add-Cyclic-Ring x y) z ＝
    add-Cyclic-Ring (mul-Cyclic-Ring x z) (mul-Cyclic-Ring y z)
  right-distributive-mul-add-Cyclic-Ring =
    right-distributive-mul-add-Ring ring-Cyclic-Ring

  is-surjective-hom-element-one-Cyclic-Ring :
    is-surjective-hom-element-Group group-Cyclic-Ring one-Cyclic-Ring
  is-surjective-hom-element-one-Cyclic-Ring x =
    apply-universal-property-trunc-Prop
      ( is-cyclic-Cyclic-Ring)
      ( trunc-Prop
        ( Σ ℤ (λ k → integer-multiple-Cyclic-Ring k one-Cyclic-Ring ＝ x)))
      ( λ (g , u) →
        apply-twice-universal-property-trunc-Prop
          ( is-surjective-hom-element-is-generating-element-Group
            ( group-Cyclic-Ring)
            ( g)
            ( u)
            ( one-Cyclic-Ring))
          ( is-surjective-hom-element-is-generating-element-Group
            ( group-Cyclic-Ring)
            ( g)
            ( u)
            ( x))
          ( trunc-Prop
            ( Σ ℤ (λ k → integer-multiple-Cyclic-Ring k one-Cyclic-Ring ＝ x)))
          ( λ { (k , p) (l , refl) →
                unit-trunc-Prop
                  {!!}}))

  is-generating-element-one-Cyclic-Ring :
    is-generating-element-Group group-Cyclic-Ring one-Cyclic-Ring
  is-generating-element-one-Cyclic-Ring x =
    apply-universal-property-trunc-Prop
      ( is-cyclic-Cyclic-Ring)
      ( trunc-Prop (Σ {!ℤ!} {!!}))
      {!!}

  commutative-mul-Cyclic-Ring :
    (x y : type-Cyclic-Ring) →
    mul-Cyclic-Ring x y ＝ mul-Cyclic-Ring y x
  commutative-mul-Cyclic-Ring x y =
    apply-universal-property-trunc-Prop
      ( is-cyclic-Cyclic-Ring)
      ( Id-Prop set-Cyclic-Ring _ _)
      ( λ (g , u) →
        {!!})
```

