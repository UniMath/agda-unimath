# Dependent products of large monoids

```agda
module group-theory.dependent-products-large-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.dependent-products-large-semigroups
open import group-theory.large-monoids
open import group-theory.large-semigroups
```

</details>

## Idea

The dependent product of a family of
[large monoids](group-theory.large-monoids.md) is a large monoid.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (M : (a : A) → Large-Monoid α β)
  where

  large-semigroup-Π-Large-Monoid :
    Large-Semigroup (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  large-semigroup-Π-Large-Monoid =
    Π-Large-Semigroup
      ( A)
      ( λ a → large-semigroup-Large-Monoid (M a))

  type-Π-Large-Monoid : (l : Level) → UU (l0 ⊔ α l)
  type-Π-Large-Monoid l = (a : A) → type-Large-Monoid (M a) l

  unit-Π-Large-Monoid : type-Π-Large-Monoid lzero
  unit-Π-Large-Monoid a = unit-Large-Monoid (M a)

  mul-Π-Large-Monoid :
    {l1 l2 : Level} →
    type-Π-Large-Monoid l1 → type-Π-Large-Monoid l2 →
    type-Π-Large-Monoid (l1 ⊔ l2)
  mul-Π-Large-Monoid = mul-Large-Semigroup large-semigroup-Π-Large-Monoid

  abstract
    left-unit-law-mul-Π-Large-Monoid :
      {l : Level} (f : type-Π-Large-Monoid l) →
      mul-Π-Large-Monoid unit-Π-Large-Monoid f ＝ f
    left-unit-law-mul-Π-Large-Monoid f =
      eq-htpy (λ a → left-unit-law-mul-Large-Monoid (M a) (f a))

    right-unit-law-mul-Π-Large-Monoid :
      {l : Level} (f : type-Π-Large-Monoid l) →
      mul-Π-Large-Monoid f unit-Π-Large-Monoid ＝ f
    right-unit-law-mul-Π-Large-Monoid f =
      eq-htpy (λ a → right-unit-law-mul-Large-Monoid (M a) (f a))

  Π-Large-Monoid : Large-Monoid (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Large-Monoid =
    λ where
      .large-semigroup-Large-Monoid → large-semigroup-Π-Large-Monoid
      .unit-Large-Monoid → unit-Π-Large-Monoid
      .left-unit-law-mul-Large-Monoid → left-unit-law-mul-Π-Large-Monoid
      .right-unit-law-mul-Large-Monoid → right-unit-law-mul-Π-Large-Monoid
```
