# Dependent products of monoids

```agda
open import foundation.function-extensionality-axiom

module
  group-theory.dependent-products-monoids
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
open import group-theory.monoids funext
open import group-theory.semigroups funext
```

</details>

## Idea

Given a family of monoids `Mᵢ` indexed by `i : I`, the dependent product
`Π(i : I), Mᵢ` is a monoid consisting of dependent functions taking `i : I` to
an element of the underlying type of `Mᵢ`. The multiplicative operation and the
unit are given pointwise.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (M : I → Monoid l2)
  where

  semigroup-Π-Monoid : Semigroup (l1 ⊔ l2)
  semigroup-Π-Monoid = Π-Semigroup I (λ i → semigroup-Monoid (M i))

  set-Π-Monoid : Set (l1 ⊔ l2)
  set-Π-Monoid = set-Semigroup semigroup-Π-Monoid

  type-Π-Monoid : UU (l1 ⊔ l2)
  type-Π-Monoid = type-Semigroup semigroup-Π-Monoid

  mul-Π-Monoid : (f g : type-Π-Monoid) → type-Π-Monoid
  mul-Π-Monoid = mul-Semigroup semigroup-Π-Monoid

  associative-mul-Π-Monoid :
    (f g h : type-Π-Monoid) →
    mul-Π-Monoid (mul-Π-Monoid f g) h ＝
    mul-Π-Monoid f (mul-Π-Monoid g h)
  associative-mul-Π-Monoid =
    associative-mul-Semigroup semigroup-Π-Monoid

  unit-Π-Monoid : type-Π-Monoid
  unit-Π-Monoid i = unit-Monoid (M i)

  left-unit-law-mul-Π-Monoid :
    (f : type-Π-Monoid) → mul-Π-Monoid unit-Π-Monoid f ＝ f
  left-unit-law-mul-Π-Monoid f =
    eq-htpy (λ i → left-unit-law-mul-Monoid (M i) (f i))

  right-unit-law-mul-Π-Monoid :
    (f : type-Π-Monoid) → mul-Π-Monoid f unit-Π-Monoid ＝ f
  right-unit-law-mul-Π-Monoid f =
    eq-htpy (λ i → right-unit-law-mul-Monoid (M i) (f i))

  is-unital-Π-Monoid : is-unital-Semigroup semigroup-Π-Monoid
  pr1 is-unital-Π-Monoid = unit-Π-Monoid
  pr1 (pr2 is-unital-Π-Monoid) = left-unit-law-mul-Π-Monoid
  pr2 (pr2 is-unital-Π-Monoid) = right-unit-law-mul-Π-Monoid

  Π-Monoid : Monoid (l1 ⊔ l2)
  pr1 Π-Monoid = semigroup-Π-Monoid
  pr2 Π-Monoid = is-unital-Π-Monoid
```
