# Dependent products of finite rings

```agda
module finite-algebra.dependent-products-finite-rings where
```

<details><summary>Imports</summary>

```agda
open import finite-algebra.finite-rings

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.dependent-products-rings
open import ring-theory.rings
open import ring-theory.semirings

open import univalent-combinatorics.dependent-function-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

Given a family of finite rings `A i` indexed by a finite type `i : I`, their
**dependent product** `Π(i:I), A i` is again a finite ring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : Finite-Type l1) (A : type-Finite-Type I → Finite-Ring l2)
  where

  semiring-Π-Finite-Ring : Semiring (l1 ⊔ l2)
  semiring-Π-Finite-Ring =
    semiring-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  ab-Π-Finite-Ring : Ab (l1 ⊔ l2)
  ab-Π-Finite-Ring = ab-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  group-Π-Finite-Ring : Group (l1 ⊔ l2)
  group-Π-Finite-Ring = group-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  semigroup-Π-Finite-Ring : Semigroup (l1 ⊔ l2)
  semigroup-Π-Finite-Ring =
    semigroup-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  multiplicative-monoid-Π-Finite-Ring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-Π-Finite-Ring =
    multiplicative-monoid-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  set-Π-Finite-Ring : Set (l1 ⊔ l2)
  set-Π-Finite-Ring = set-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  type-Π-Finite-Ring : UU (l1 ⊔ l2)
  type-Π-Finite-Ring = type-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  is-finite-type-Π-Finite-Ring : is-finite (type-Π-Finite-Ring)
  is-finite-type-Π-Finite-Ring =
    is-finite-Π
      ( is-finite-type-Finite-Type I)
      ( λ i → is-finite-type-Finite-Ring (A i))

  finite-type-Π-Finite-Ring : Finite-Type (l1 ⊔ l2)
  pr1 finite-type-Π-Finite-Ring = type-Π-Finite-Ring
  pr2 finite-type-Π-Finite-Ring = is-finite-type-Π-Finite-Ring

  is-set-type-Π-Finite-Ring : is-set type-Π-Finite-Ring
  is-set-type-Π-Finite-Ring =
    is-set-type-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  add-Π-Finite-Ring :
    type-Π-Finite-Ring → type-Π-Finite-Ring → type-Π-Finite-Ring
  add-Π-Finite-Ring = add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  zero-Π-Finite-Ring : type-Π-Finite-Ring
  zero-Π-Finite-Ring = zero-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  neg-Π-Finite-Ring : type-Π-Finite-Ring → type-Π-Finite-Ring
  neg-Π-Finite-Ring = neg-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  associative-add-Π-Finite-Ring :
    (x y z : type-Π-Finite-Ring) →
    Id
      ( add-Π-Finite-Ring (add-Π-Finite-Ring x y) z)
      ( add-Π-Finite-Ring x (add-Π-Finite-Ring y z))
  associative-add-Π-Finite-Ring =
    associative-add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  left-unit-law-add-Π-Finite-Ring :
    (x : type-Π-Finite-Ring) → add-Π-Finite-Ring zero-Π-Finite-Ring x ＝ x
  left-unit-law-add-Π-Finite-Ring =
    left-unit-law-add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  right-unit-law-add-Π-Finite-Ring :
    (x : type-Π-Finite-Ring) → add-Π-Finite-Ring x zero-Π-Finite-Ring ＝ x
  right-unit-law-add-Π-Finite-Ring =
    right-unit-law-add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  left-inverse-law-add-Π-Finite-Ring :
    (x : type-Π-Finite-Ring) →
    add-Π-Finite-Ring (neg-Π-Finite-Ring x) x ＝ zero-Π-Finite-Ring
  left-inverse-law-add-Π-Finite-Ring =
    left-inverse-law-add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  right-inverse-law-add-Π-Finite-Ring :
    (x : type-Π-Finite-Ring) →
    add-Π-Finite-Ring x (neg-Π-Finite-Ring x) ＝ zero-Π-Finite-Ring
  right-inverse-law-add-Π-Finite-Ring =
    right-inverse-law-add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  commutative-add-Π-Finite-Ring :
    (x y : type-Π-Finite-Ring) →
    add-Π-Finite-Ring x y ＝ add-Π-Finite-Ring y x
  commutative-add-Π-Finite-Ring =
    commutative-add-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  mul-Π-Finite-Ring :
    type-Π-Finite-Ring → type-Π-Finite-Ring → type-Π-Finite-Ring
  mul-Π-Finite-Ring = mul-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  one-Π-Finite-Ring : type-Π-Finite-Ring
  one-Π-Finite-Ring = one-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  associative-mul-Π-Finite-Ring :
    (x y z : type-Π-Finite-Ring) →
    Id
      ( mul-Π-Finite-Ring (mul-Π-Finite-Ring x y) z)
      ( mul-Π-Finite-Ring x (mul-Π-Finite-Ring y z))
  associative-mul-Π-Finite-Ring =
    associative-mul-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  left-unit-law-mul-Π-Finite-Ring :
    (x : type-Π-Finite-Ring) → mul-Π-Finite-Ring one-Π-Finite-Ring x ＝ x
  left-unit-law-mul-Π-Finite-Ring =
    left-unit-law-mul-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  right-unit-law-mul-Π-Finite-Ring :
    (x : type-Π-Finite-Ring) → mul-Π-Finite-Ring x one-Π-Finite-Ring ＝ x
  right-unit-law-mul-Π-Finite-Ring =
    right-unit-law-mul-Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  left-distributive-mul-add-Π-Finite-Ring :
    (f g h : type-Π-Finite-Ring) →
    mul-Π-Finite-Ring f (add-Π-Finite-Ring g h) ＝
    add-Π-Finite-Ring (mul-Π-Finite-Ring f g) (mul-Π-Finite-Ring f h)
  left-distributive-mul-add-Π-Finite-Ring =
    left-distributive-mul-add-Π-Ring
      ( type-Finite-Type I)
      ( ring-Finite-Ring ∘ A)

  right-distributive-mul-add-Π-Finite-Ring :
    (f g h : type-Π-Finite-Ring) →
    Id
      ( mul-Π-Finite-Ring (add-Π-Finite-Ring f g) h)
      ( add-Π-Finite-Ring (mul-Π-Finite-Ring f h) (mul-Π-Finite-Ring g h))
  right-distributive-mul-add-Π-Finite-Ring =
    right-distributive-mul-add-Π-Ring
      ( type-Finite-Type I)
      ( ring-Finite-Ring ∘ A)

  ring-Π-Finite-Ring : Ring (l1 ⊔ l2)
  ring-Π-Finite-Ring = Π-Ring (type-Finite-Type I) (ring-Finite-Ring ∘ A)

  Π-Finite-Ring : Finite-Ring (l1 ⊔ l2)
  Π-Finite-Ring =
    finite-ring-is-finite-Ring ring-Π-Finite-Ring is-finite-type-Π-Finite-Ring
```
