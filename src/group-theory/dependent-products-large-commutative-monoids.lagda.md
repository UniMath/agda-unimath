# Dependent products of large commutative monoids

```agda
module group-theory.dependent-products-large-commutative-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.dependent-products-large-monoids
open import group-theory.large-commutative-monoids
open import group-theory.large-monoids
```

</details>

## Idea

The dependent product of a family of
[large commutative monoids](group-theory.large-commutative-monoids.md) is a
large commutative monoid.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  {l0 : Level}
  (A : UU l0)
  (M : (a : A) → Large-Commutative-Monoid α β)
  where

  large-monoid-Π-Large-Commutative-Monoid :
    Large-Monoid (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  large-monoid-Π-Large-Commutative-Monoid =
    Π-Large-Monoid A (λ a → large-monoid-Large-Commutative-Monoid (M a))

  type-Π-Large-Commutative-Monoid :
    (l : Level) → UU (l0 ⊔ α l)
  type-Π-Large-Commutative-Monoid l =
    (a : A) → type-Large-Commutative-Monoid (M a) l

  mul-Π-Large-Commutative-Monoid :
    {l1 l2 : Level} →
    type-Π-Large-Commutative-Monoid l1 → type-Π-Large-Commutative-Monoid l2 →
    type-Π-Large-Commutative-Monoid (l1 ⊔ l2)
  mul-Π-Large-Commutative-Monoid f g a =
    mul-Large-Commutative-Monoid (M a) (f a) (g a)

  abstract
    commutative-mul-Π-Large-Commutative-Monoid :
      {l1 l2 : Level}
      (f : type-Π-Large-Commutative-Monoid l1)
      (g : type-Π-Large-Commutative-Monoid l2) →
      mul-Π-Large-Commutative-Monoid f g ＝ mul-Π-Large-Commutative-Monoid g f
    commutative-mul-Π-Large-Commutative-Monoid f g =
      eq-htpy (λ a → commutative-mul-Large-Commutative-Monoid (M a) (f a) (g a))

  Π-Large-Commutative-Monoid :
    Large-Commutative-Monoid (λ l → l0 ⊔ α l) (λ l1 l2 → l0 ⊔ β l1 l2)
  Π-Large-Commutative-Monoid =
    λ where
      .large-monoid-Large-Commutative-Monoid →
        large-monoid-Π-Large-Commutative-Monoid
      .commutative-mul-Large-Commutative-Monoid →
        commutative-mul-Π-Large-Commutative-Monoid
```
