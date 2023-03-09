# Dependent products of rings

```agda
module ring-theory.dependent-products-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.groups
open import group-theory.semigroups

open import ring-theory.rings
```

</details>

## Idea

Given a family of rings `R i` indexed by `i : I`, their dependent product `Π(i:I), R i` is again a ring.

## Definition

```agda
module _
  {l1 l2 : Level} {I : UU l1} (R : I → Ring l2)
  where

  set-Π-Ring : Set (l1 ⊔ l2)
  set-Π-Ring = Π-Set' I (λ i → set-Ring (R i))

  type-Π-Ring : UU (l1 ⊔ l2)
  type-Π-Ring = type-Set set-Π-Ring

  is-set-type-Π-Ring : is-set type-Π-Ring
  is-set-type-Π-Ring = is-set-type-Set set-Π-Ring

  add-Π-Ring : type-Π-Ring → type-Π-Ring → type-Π-Ring
  add-Π-Ring x y i = add-Ring (R i) (x i) (y i)

  zero-Π-Ring : type-Π-Ring
  zero-Π-Ring i = zero-Ring (R i)

  neg-Π-Ring : type-Π-Ring → type-Π-Ring
  neg-Π-Ring x i = neg-Ring (R i) (x i)

  associative-add-Π-Ring :
    (x y z : type-Π-Ring) →
    Id (add-Π-Ring (add-Π-Ring x y) z) (add-Π-Ring x (add-Π-Ring y z))
  associative-add-Π-Ring x y z =
    eq-htpy (λ i → associative-add-Ring (R i) (x i) (y i) (z i))

  left-unit-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring zero-Π-Ring x) x
  left-unit-law-add-Π-Ring x =
    eq-htpy (λ i → left-unit-law-add-Ring (R i) (x i))

  right-unit-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring x zero-Π-Ring) x
  right-unit-law-add-Π-Ring x =
    eq-htpy (λ i → right-unit-law-add-Ring (R i) (x i))

  left-inverse-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring (neg-Π-Ring x) x) zero-Π-Ring
  left-inverse-law-add-Π-Ring x =
    eq-htpy (λ i → left-inverse-law-add-Ring (R i) (x i))

  right-inverse-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring x (neg-Π-Ring x)) zero-Π-Ring
  right-inverse-law-add-Π-Ring x =
    eq-htpy (λ i → right-inverse-law-add-Ring (R i) (x i))

  commutative-add-Π-Ring :
    (x y : type-Π-Ring) → Id (add-Π-Ring x y) (add-Π-Ring y x)
  commutative-add-Π-Ring x y =
    eq-htpy (λ i → commutative-add-Ring (R i) (x i) (y i))

  mul-Π-Ring : type-Π-Ring → type-Π-Ring → type-Π-Ring
  mul-Π-Ring x y i = mul-Ring (R i) (x i) (y i)

  one-Π-Ring : type-Π-Ring
  one-Π-Ring i = one-Ring (R i)

  associative-mul-Π-Ring :
    (x y z : type-Π-Ring) →
    Id (mul-Π-Ring (mul-Π-Ring x y) z) (mul-Π-Ring x (mul-Π-Ring y z))
  associative-mul-Π-Ring x y z =
    eq-htpy (λ i → associative-mul-Ring (R i) (x i) (y i) (z i))

  left-unit-law-mul-Π-Ring :
    (x : type-Π-Ring) → Id (mul-Π-Ring one-Π-Ring x) x
  left-unit-law-mul-Π-Ring x =
    eq-htpy (λ i → left-unit-law-mul-Ring (R i) (x i))

  right-unit-law-mul-Π-Ring :
    (x : type-Π-Ring) → Id (mul-Π-Ring x one-Π-Ring) x
  right-unit-law-mul-Π-Ring x =
    eq-htpy (λ i → right-unit-law-mul-Ring (R i) (x i))

  left-distributive-mul-add-Π-Ring :
    (x y z : type-Π-Ring) →
    Id ( mul-Π-Ring x (add-Π-Ring y z))
       ( add-Π-Ring (mul-Π-Ring x y) (mul-Π-Ring x z))
  left-distributive-mul-add-Π-Ring x y z =
    eq-htpy (λ i → left-distributive-mul-add-Ring (R i) (x i) (y i) (z i))

  right-distributive-mul-add-Π-Ring :
    (x y z : type-Π-Ring) →
    Id ( mul-Π-Ring (add-Π-Ring x y) z)
       ( add-Π-Ring (mul-Π-Ring x z) (mul-Π-Ring y z))
  right-distributive-mul-add-Π-Ring x y z =
    eq-htpy (λ i → right-distributive-mul-add-Ring (R i) (x i) (y i) (z i))

  semigroup-Π-Ring : Semigroup (l1 ⊔ l2)
  pr1 semigroup-Π-Ring = set-Π-Ring
  pr1 (pr2 semigroup-Π-Ring) = add-Π-Ring
  pr2 (pr2 semigroup-Π-Ring) = associative-add-Π-Ring

  group-Π-Ring : Group (l1 ⊔ l2)
  pr1 group-Π-Ring = semigroup-Π-Ring
  pr1 (pr1 (pr2 group-Π-Ring)) = zero-Π-Ring
  pr1 (pr2 (pr1 (pr2 group-Π-Ring))) = left-unit-law-add-Π-Ring
  pr2 (pr2 (pr1 (pr2 group-Π-Ring))) = right-unit-law-add-Π-Ring
  pr1 (pr2 (pr2 group-Π-Ring)) = neg-Π-Ring
  pr1 (pr2 (pr2 (pr2 group-Π-Ring))) = left-inverse-law-add-Π-Ring
  pr2 (pr2 (pr2 (pr2 group-Π-Ring))) = right-inverse-law-add-Π-Ring

  ab-Π-Ring : Ab (l1 ⊔ l2)
  pr1 ab-Π-Ring = group-Π-Ring
  pr2 ab-Π-Ring = commutative-add-Π-Ring

  Π-Ring : Ring (l1 ⊔ l2)
  pr1 Π-Ring = ab-Π-Ring
  pr1 (pr1 (pr2 Π-Ring)) = mul-Π-Ring
  pr2 (pr1 (pr2 Π-Ring)) = associative-mul-Π-Ring
  pr1 (pr1 (pr2 (pr2 Π-Ring))) = one-Π-Ring
  pr1 (pr2 (pr1 (pr2 (pr2 Π-Ring)))) = left-unit-law-mul-Π-Ring
  pr2 (pr2 (pr1 (pr2 (pr2 Π-Ring)))) = right-unit-law-mul-Π-Ring
  pr1 (pr2 (pr2 (pr2 Π-Ring))) = left-distributive-mul-add-Π-Ring
  pr2 (pr2 (pr2 (pr2 Π-Ring))) = right-distributive-mul-add-Π-Ring
```
