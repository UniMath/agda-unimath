# Monoids

```agda
module group-theory.monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.semigroups
```

</details>

## Idea

Monoids are unital semigroups

## Definition

```agda
is-unital-Semigroup :
  {l : Level} → Semigroup l → UU l
is-unital-Semigroup G = is-unital (mul-Semigroup G)

Monoid :
  (l : Level) → UU (lsuc l)
Monoid l = Σ (Semigroup l) is-unital-Semigroup

module _
  {l : Level} (M : Monoid l)
  where

  semigroup-Monoid : Semigroup l
  semigroup-Monoid = pr1 M

  type-Monoid : UU l
  type-Monoid = type-Semigroup semigroup-Monoid

  set-Monoid : Set l
  set-Monoid = set-Semigroup semigroup-Monoid

  is-set-type-Monoid : is-set type-Monoid
  is-set-type-Monoid = is-set-type-Semigroup semigroup-Monoid

  mul-Monoid : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid = mul-Semigroup semigroup-Monoid

  mul-Monoid' : type-Monoid → type-Monoid → type-Monoid
  mul-Monoid' y x = mul-Monoid x y

  ap-mul-Monoid :
    {x x' y y' : type-Monoid} →
    x ＝ x' → y ＝ y' → mul-Monoid x y ＝ mul-Monoid x' y'
  ap-mul-Monoid = ap-mul-Semigroup semigroup-Monoid

  associative-mul-Monoid :
    (x y z : type-Monoid) →
    mul-Monoid (mul-Monoid x y) z ＝ mul-Monoid x (mul-Monoid y z)
  associative-mul-Monoid = associative-mul-Semigroup semigroup-Monoid

  has-unit-Monoid : is-unital mul-Monoid
  has-unit-Monoid = pr2 M

  unit-Monoid : type-Monoid
  unit-Monoid = pr1 has-unit-Monoid

  left-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid unit-Monoid x ＝ x
  left-unit-law-mul-Monoid = pr1 (pr2 has-unit-Monoid)

  right-unit-law-mul-Monoid : (x : type-Monoid) → mul-Monoid x unit-Monoid ＝ x
  right-unit-law-mul-Monoid = pr2 (pr2 has-unit-Monoid)
```

## Properties

### For any semigroup `G`, being unital is a property

```agda
abstract
  all-elements-equal-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → all-elements-equal (is-unital-Semigroup G)
  all-elements-equal-is-unital-Semigroup (pair X (pair μ associative-μ))
    (pair e (pair left-unit-e right-unit-e))
    (pair e' (pair left-unit-e' right-unit-e')) =
    eq-type-subtype
      ( λ e →
        prod-Prop
          ( Π-Prop (type-Set X) (λ y → Id-Prop X (μ e y) y))
          ( Π-Prop (type-Set X) (λ x → Id-Prop X (μ x e) x)))
      ( (inv (left-unit-e' e)) ∙ (right-unit-e e'))

abstract
  is-prop-is-unital-Semigroup :
    {l : Level} (G : Semigroup l) → is-prop (is-unital-Semigroup G)
  is-prop-is-unital-Semigroup G =
    is-prop-all-elements-equal (all-elements-equal-is-unital-Semigroup G)

is-unital-Semigroup-Prop : {l : Level} (G : Semigroup l) → Prop l
pr1 (is-unital-Semigroup-Prop G) = is-unital-Semigroup G
pr2 (is-unital-Semigroup-Prop G) = is-prop-is-unital-Semigroup G
```
