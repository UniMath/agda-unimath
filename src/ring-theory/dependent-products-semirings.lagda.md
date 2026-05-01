# Dependent products of semirings

```agda
module ring-theory.dependent-products-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.dependent-products-commutative-monoids
open import group-theory.dependent-products-monoids
open import group-theory.monoids
open import group-theory.semigroups

open import ring-theory.semirings
```

</details>

## Idea

Given a family of [semirings](ring-theory.semirings.md) `R i` indexed by
`i : I`, their
{{#concept "dependent product" Disambiguation="semiring" Agda=Π-Semiring}}
`Π(i:I), R i` is again a semiring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (R : I → Semiring l2)
  where

  additive-commutative-monoid-Π-Semiring : Commutative-Monoid (l1 ⊔ l2)
  additive-commutative-monoid-Π-Semiring =
    Π-Commutative-Monoid I
      ( λ i → additive-commutative-monoid-Semiring (R i))

  semigroup-Π-Semiring : Semigroup (l1 ⊔ l2)
  semigroup-Π-Semiring =
    semigroup-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  multiplicative-monoid-Π-Semiring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-Π-Semiring =
    Π-Monoid I (λ i → multiplicative-monoid-Semiring (R i))

  set-Π-Semiring : Set (l1 ⊔ l2)
  set-Π-Semiring =
    set-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  type-Π-Semiring : UU (l1 ⊔ l2)
  type-Π-Semiring =
    type-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  is-set-type-Π-Semiring : is-set type-Π-Semiring
  is-set-type-Π-Semiring =
    is-set-type-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  add-Π-Semiring : type-Π-Semiring → type-Π-Semiring → type-Π-Semiring
  add-Π-Semiring =
    mul-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  zero-Π-Semiring : type-Π-Semiring
  zero-Π-Semiring =
    unit-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  associative-add-Π-Semiring :
    (x y z : type-Π-Semiring) →
    add-Π-Semiring (add-Π-Semiring x y) z ＝
    add-Π-Semiring x (add-Π-Semiring y z)
  associative-add-Π-Semiring =
    associative-mul-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  left-unit-law-add-Π-Semiring :
    (x : type-Π-Semiring) → add-Π-Semiring zero-Π-Semiring x ＝ x
  left-unit-law-add-Π-Semiring =
    left-unit-law-mul-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  right-unit-law-add-Π-Semiring :
    (x : type-Π-Semiring) → add-Π-Semiring x zero-Π-Semiring ＝ x
  right-unit-law-add-Π-Semiring =
    right-unit-law-mul-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  commutative-add-Π-Semiring :
    (x y : type-Π-Semiring) → add-Π-Semiring x y ＝ add-Π-Semiring y x
  commutative-add-Π-Semiring =
    commutative-mul-Commutative-Monoid additive-commutative-monoid-Π-Semiring

  mul-Π-Semiring : type-Π-Semiring → type-Π-Semiring → type-Π-Semiring
  mul-Π-Semiring = mul-Monoid multiplicative-monoid-Π-Semiring

  one-Π-Semiring : type-Π-Semiring
  one-Π-Semiring = unit-Monoid multiplicative-monoid-Π-Semiring

  associative-mul-Π-Semiring :
    (x y z : type-Π-Semiring) →
    mul-Π-Semiring (mul-Π-Semiring x y) z ＝
    mul-Π-Semiring x (mul-Π-Semiring y z)
  associative-mul-Π-Semiring =
    associative-mul-Monoid multiplicative-monoid-Π-Semiring

  left-unit-law-mul-Π-Semiring :
    (x : type-Π-Semiring) → mul-Π-Semiring one-Π-Semiring x ＝ x
  left-unit-law-mul-Π-Semiring =
    left-unit-law-mul-Monoid multiplicative-monoid-Π-Semiring

  right-unit-law-mul-Π-Semiring :
    (x : type-Π-Semiring) → mul-Π-Semiring x one-Π-Semiring ＝ x
  right-unit-law-mul-Π-Semiring =
    right-unit-law-mul-Monoid multiplicative-monoid-Π-Semiring

  left-distributive-mul-add-Π-Semiring :
    (f g h : type-Π-Semiring) →
    mul-Π-Semiring f (add-Π-Semiring g h) ＝
    add-Π-Semiring (mul-Π-Semiring f g) (mul-Π-Semiring f h)
  left-distributive-mul-add-Π-Semiring f g h =
    eq-htpy (λ i → left-distributive-mul-add-Semiring (R i) (f i) (g i) (h i))

  right-distributive-mul-add-Π-Semiring :
    (f g h : type-Π-Semiring) →
    mul-Π-Semiring (add-Π-Semiring f g) h ＝
    add-Π-Semiring (mul-Π-Semiring f h) (mul-Π-Semiring g h)
  right-distributive-mul-add-Π-Semiring f g h =
    eq-htpy (λ i → right-distributive-mul-add-Semiring (R i) (f i) (g i) (h i))

  left-zero-law-mul-Π-Semiring :
    (f : type-Π-Semiring) →
    mul-Π-Semiring zero-Π-Semiring f ＝ zero-Π-Semiring
  left-zero-law-mul-Π-Semiring f =
    eq-htpy (λ i → left-zero-law-mul-Semiring (R i) (f i))

  right-zero-law-mul-Π-Semiring :
    (f : type-Π-Semiring) →
    mul-Π-Semiring f zero-Π-Semiring ＝ zero-Π-Semiring
  right-zero-law-mul-Π-Semiring f =
    eq-htpy (λ i → right-zero-law-mul-Semiring (R i) (f i))

  Π-Semiring : Semiring (l1 ⊔ l2)
  pr1 Π-Semiring = additive-commutative-monoid-Π-Semiring
  pr1 (pr1 (pr1 (pr2 Π-Semiring))) = mul-Π-Semiring
  pr2 (pr1 (pr1 (pr2 Π-Semiring))) = associative-mul-Π-Semiring
  pr1 (pr1 (pr2 (pr1 (pr2 Π-Semiring)))) = one-Π-Semiring
  pr1 (pr2 (pr1 (pr2 (pr1 (pr2 Π-Semiring))))) = left-unit-law-mul-Π-Semiring
  pr2 (pr2 (pr1 (pr2 (pr1 (pr2 Π-Semiring))))) = right-unit-law-mul-Π-Semiring
  pr1 (pr2 (pr2 (pr1 (pr2 Π-Semiring)))) = left-distributive-mul-add-Π-Semiring
  pr2 (pr2 (pr2 (pr1 (pr2 Π-Semiring)))) = right-distributive-mul-add-Π-Semiring
  pr1 (pr2 (pr2 Π-Semiring)) = left-zero-law-mul-Π-Semiring
  pr2 (pr2 (pr2 Π-Semiring)) = right-zero-law-mul-Π-Semiring
```
