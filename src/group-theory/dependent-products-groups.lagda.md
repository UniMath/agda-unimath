# Dependent products of groups

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.dependent-products-groups
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality funext

open import foundation.identity-types funext
open import foundation.sets funext
open import foundation.universe-levels

open import group-theory.dependent-products-semigroups funext
open import group-theory.groups funext
open import group-theory.monoids funext
open import group-theory.semigroups funext
```

</details>

## Idea

Given a family of groups `Gᵢ` indexed by `i : I`, the dependent product
`Π(i : I), Gᵢ` is a group consisting of dependent functions taking `i : I` to an
element of the underlying type of `Gᵢ`. The multiplicative operation and the
unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (G : I → Group l2)
  where

  semigroup-Π-Group : Semigroup (l1 ⊔ l2)
  semigroup-Π-Group = Π-Semigroup I (λ i → semigroup-Group (G i))

  set-Π-Group : Set (l1 ⊔ l2)
  set-Π-Group = set-Semigroup semigroup-Π-Group

  type-Π-Group : UU (l1 ⊔ l2)
  type-Π-Group = type-Semigroup semigroup-Π-Group

  mul-Π-Group : (f g : type-Π-Group) → type-Π-Group
  mul-Π-Group = mul-Semigroup semigroup-Π-Group

  associative-mul-Π-Group :
    (f g h : type-Π-Group) →
    mul-Π-Group (mul-Π-Group f g) h ＝
    mul-Π-Group f (mul-Π-Group g h)
  associative-mul-Π-Group =
    associative-mul-Semigroup semigroup-Π-Group

  unit-Π-Group : type-Π-Group
  unit-Π-Group i = unit-Group (G i)

  left-unit-law-mul-Π-Group :
    (f : type-Π-Group) → mul-Π-Group unit-Π-Group f ＝ f
  left-unit-law-mul-Π-Group f =
    eq-htpy (λ i → left-unit-law-mul-Group (G i) (f i))

  right-unit-law-mul-Π-Group :
    (f : type-Π-Group) → mul-Π-Group f unit-Π-Group ＝ f
  right-unit-law-mul-Π-Group f =
    eq-htpy (λ i → right-unit-law-mul-Group (G i) (f i))

  is-unital-Π-Group : is-unital-Semigroup semigroup-Π-Group
  pr1 is-unital-Π-Group = unit-Π-Group
  pr1 (pr2 is-unital-Π-Group) = left-unit-law-mul-Π-Group
  pr2 (pr2 is-unital-Π-Group) = right-unit-law-mul-Π-Group

  monoid-Π-Group : Monoid (l1 ⊔ l2)
  pr1 monoid-Π-Group = semigroup-Π-Group
  pr2 monoid-Π-Group = is-unital-Π-Group

  inv-Π-Group : type-Π-Group → type-Π-Group
  inv-Π-Group f x = inv-Group (G x) (f x)

  left-inverse-law-mul-Π-Group :
    (f : type-Π-Group) →
    mul-Π-Group (inv-Π-Group f) f ＝ unit-Π-Group
  left-inverse-law-mul-Π-Group f =
    eq-htpy (λ x → left-inverse-law-mul-Group (G x) (f x))

  right-inverse-law-mul-Π-Group :
    (f : type-Π-Group) →
    mul-Π-Group f (inv-Π-Group f) ＝ unit-Π-Group
  right-inverse-law-mul-Π-Group f =
    eq-htpy (λ x → right-inverse-law-mul-Group (G x) (f x))

  is-group-Π-Group : is-group-Semigroup semigroup-Π-Group
  pr1 is-group-Π-Group = is-unital-Π-Group
  pr1 (pr2 is-group-Π-Group) = inv-Π-Group
  pr1 (pr2 (pr2 is-group-Π-Group)) = left-inverse-law-mul-Π-Group
  pr2 (pr2 (pr2 is-group-Π-Group)) = right-inverse-law-mul-Π-Group

  Π-Group : Group (l1 ⊔ l2)
  pr1 Π-Group = semigroup-Π-Group
  pr2 Π-Group = is-group-Π-Group
```
