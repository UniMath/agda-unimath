# Dependent products of large rings

```agda
module ring-theory.dependent-products-large-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.dependent-products-large-abelian-groups
open import group-theory.dependent-products-large-monoids
open import group-theory.large-abelian-groups
open import group-theory.large-monoids

open import ring-theory.large-rings
```

</details>

## Idea

The dependent product of a family of [large rings](ring-theory.large-rings.md)
is a large ring.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (R : A → Large-Ring α β)
  where

  large-ab-Π-Large-Ring : Large-Ab (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  large-ab-Π-Large-Ring =
    Π-Large-Ab A (λ a → large-ab-Large-Ring (R a))

  large-monoid-mul-Π-Large-Ring :
    Large-Monoid (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  large-monoid-mul-Π-Large-Ring =
    Π-Large-Monoid A (λ a → large-monoid-mul-Large-Ring (R a))

  type-Π-Large-Ring : (l : Level) → UU (l0 ⊔ α l)
  type-Π-Large-Ring l = (a : A) → type-Large-Ring (R a) l

  add-Π-Large-Ring :
    {l1 l2 : Level} →
    type-Π-Large-Ring l1 → type-Π-Large-Ring l2 → type-Π-Large-Ring (l1 ⊔ l2)
  add-Π-Large-Ring = add-Large-Ab large-ab-Π-Large-Ring

  mul-Π-Large-Ring :
    {l1 l2 : Level} →
    type-Π-Large-Ring l1 → type-Π-Large-Ring l2 → type-Π-Large-Ring (l1 ⊔ l2)
  mul-Π-Large-Ring = mul-Large-Monoid large-monoid-mul-Π-Large-Ring

  one-Π-Large-Ring : type-Π-Large-Ring lzero
  one-Π-Large-Ring = unit-Large-Monoid large-monoid-mul-Π-Large-Ring

  associative-mul-Π-Large-Ring :
    {l1 l2 l3 : Level}
    (x : type-Π-Large-Ring l1)
    (y : type-Π-Large-Ring l2)
    (z : type-Π-Large-Ring l3) →
    mul-Π-Large-Ring (mul-Π-Large-Ring x y) z ＝
    mul-Π-Large-Ring x (mul-Π-Large-Ring y z)
  associative-mul-Π-Large-Ring =
    associative-mul-Large-Monoid large-monoid-mul-Π-Large-Ring

  left-unit-law-mul-Π-Large-Ring :
    {l : Level} (x : type-Π-Large-Ring l) →
    mul-Π-Large-Ring one-Π-Large-Ring x ＝ x
  left-unit-law-mul-Π-Large-Ring =
    left-unit-law-mul-Large-Monoid large-monoid-mul-Π-Large-Ring

  right-unit-law-mul-Π-Large-Ring :
    {l : Level} (x : type-Π-Large-Ring l) →
    mul-Π-Large-Ring x one-Π-Large-Ring ＝ x
  right-unit-law-mul-Π-Large-Ring =
    right-unit-law-mul-Large-Monoid large-monoid-mul-Π-Large-Ring

  abstract
    left-distributive-mul-add-Π-Large-Ring :
      {l1 l2 l3 : Level}
      (x : type-Π-Large-Ring l1)
      (y : type-Π-Large-Ring l2)
      (z : type-Π-Large-Ring l3) →
      mul-Π-Large-Ring x (add-Π-Large-Ring y z) ＝
      add-Π-Large-Ring (mul-Π-Large-Ring x y) (mul-Π-Large-Ring x z)
    left-distributive-mul-add-Π-Large-Ring x y z =
      eq-htpy
        ( λ a → left-distributive-mul-add-Large-Ring (R a) (x a) (y a) (z a))

    right-distributive-mul-add-Π-Large-Ring :
      {l1 l2 l3 : Level}
      (x : type-Π-Large-Ring l1)
      (y : type-Π-Large-Ring l2)
      (z : type-Π-Large-Ring l3) →
      mul-Π-Large-Ring (add-Π-Large-Ring x y) z ＝
      add-Π-Large-Ring (mul-Π-Large-Ring x z) (mul-Π-Large-Ring y z)
    right-distributive-mul-add-Π-Large-Ring x y z =
      eq-htpy
        ( λ a → right-distributive-mul-add-Large-Ring (R a) (x a) (y a) (z a))

  Π-Large-Ring : Large-Ring (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Large-Ring =
    λ where
      .large-ab-Large-Ring →
        large-ab-Π-Large-Ring
      .sim-preserving-binary-operator-mul-Large-Ring →
        sim-preserving-binary-operator-mul-Large-Monoid
          ( large-monoid-mul-Π-Large-Ring)
      .one-Large-Ring →
        one-Π-Large-Ring
      .associative-mul-Large-Ring →
        associative-mul-Π-Large-Ring
      .left-unit-law-mul-Large-Ring →
        left-unit-law-mul-Π-Large-Ring
      .right-unit-law-mul-Large-Ring →
        right-unit-law-mul-Π-Large-Ring
      .left-distributive-mul-add-Large-Ring →
        left-distributive-mul-add-Π-Large-Ring
      .right-distributive-mul-add-Large-Ring →
        right-distributive-mul-add-Π-Large-Ring
```
