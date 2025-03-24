# Dependent products of rings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.dependent-products-rings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.abelian-groups funext univalence truncations
open import group-theory.dependent-products-abelian-groups funext univalence truncations
open import group-theory.groups funext univalence truncations
open import group-theory.monoids funext univalence truncations
open import group-theory.semigroups funext univalence

open import ring-theory.dependent-products-semirings funext univalence truncations
open import ring-theory.rings funext univalence truncations
open import ring-theory.semirings funext univalence truncations
```

</details>

## Idea

Given a family of rings `R i` indexed by `i : I`, their dependent product
`Π(i:I), R i` is again a ring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (R : I → Ring l2)
  where

  semiring-Π-Ring : Semiring (l1 ⊔ l2)
  semiring-Π-Ring = Π-Semiring I (λ i → semiring-Ring (R i))

  ab-Π-Ring : Ab (l1 ⊔ l2)
  ab-Π-Ring = Π-Ab I (λ i → ab-Ring (R i))

  group-Π-Ring : Group (l1 ⊔ l2)
  group-Π-Ring = group-Ab ab-Π-Ring

  semigroup-Π-Ring : Semigroup (l1 ⊔ l2)
  semigroup-Π-Ring = semigroup-Ab ab-Π-Ring

  multiplicative-monoid-Π-Ring : Monoid (l1 ⊔ l2)
  multiplicative-monoid-Π-Ring =
    multiplicative-monoid-Semiring semiring-Π-Ring

  set-Π-Ring : Set (l1 ⊔ l2)
  set-Π-Ring = set-Semiring semiring-Π-Ring

  type-Π-Ring : UU (l1 ⊔ l2)
  type-Π-Ring = type-Semiring semiring-Π-Ring

  is-set-type-Π-Ring : is-set type-Π-Ring
  is-set-type-Π-Ring = is-set-type-Semiring semiring-Π-Ring

  add-Π-Ring : type-Π-Ring → type-Π-Ring → type-Π-Ring
  add-Π-Ring = add-Semiring semiring-Π-Ring

  zero-Π-Ring : type-Π-Ring
  zero-Π-Ring = zero-Semiring semiring-Π-Ring

  neg-Π-Ring : type-Π-Ring → type-Π-Ring
  neg-Π-Ring = neg-Ab ab-Π-Ring

  associative-add-Π-Ring :
    (x y z : type-Π-Ring) →
    Id (add-Π-Ring (add-Π-Ring x y) z) (add-Π-Ring x (add-Π-Ring y z))
  associative-add-Π-Ring = associative-add-Semiring semiring-Π-Ring

  left-unit-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring zero-Π-Ring x) x
  left-unit-law-add-Π-Ring = left-unit-law-add-Semiring semiring-Π-Ring

  right-unit-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring x zero-Π-Ring) x
  right-unit-law-add-Π-Ring = right-unit-law-add-Semiring semiring-Π-Ring

  left-inverse-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring (neg-Π-Ring x) x) zero-Π-Ring
  left-inverse-law-add-Π-Ring = left-inverse-law-add-Ab ab-Π-Ring

  right-inverse-law-add-Π-Ring :
    (x : type-Π-Ring) → Id (add-Π-Ring x (neg-Π-Ring x)) zero-Π-Ring
  right-inverse-law-add-Π-Ring = right-inverse-law-add-Ab ab-Π-Ring

  commutative-add-Π-Ring :
    (x y : type-Π-Ring) → Id (add-Π-Ring x y) (add-Π-Ring y x)
  commutative-add-Π-Ring = commutative-add-Semiring semiring-Π-Ring

  mul-Π-Ring : type-Π-Ring → type-Π-Ring → type-Π-Ring
  mul-Π-Ring = mul-Semiring semiring-Π-Ring

  one-Π-Ring : type-Π-Ring
  one-Π-Ring = one-Semiring semiring-Π-Ring

  associative-mul-Π-Ring :
    (x y z : type-Π-Ring) →
    Id (mul-Π-Ring (mul-Π-Ring x y) z) (mul-Π-Ring x (mul-Π-Ring y z))
  associative-mul-Π-Ring =
    associative-mul-Semiring semiring-Π-Ring

  left-unit-law-mul-Π-Ring :
    (x : type-Π-Ring) → Id (mul-Π-Ring one-Π-Ring x) x
  left-unit-law-mul-Π-Ring =
    left-unit-law-mul-Semiring semiring-Π-Ring

  right-unit-law-mul-Π-Ring :
    (x : type-Π-Ring) → Id (mul-Π-Ring x one-Π-Ring) x
  right-unit-law-mul-Π-Ring =
    right-unit-law-mul-Semiring semiring-Π-Ring

  left-distributive-mul-add-Π-Ring :
    (f g h : type-Π-Ring) →
    mul-Π-Ring f (add-Π-Ring g h) ＝
    add-Π-Ring (mul-Π-Ring f g) (mul-Π-Ring f h)
  left-distributive-mul-add-Π-Ring =
    left-distributive-mul-add-Semiring semiring-Π-Ring

  right-distributive-mul-add-Π-Ring :
    (f g h : type-Π-Ring) →
    Id
      ( mul-Π-Ring (add-Π-Ring f g) h)
      ( add-Π-Ring (mul-Π-Ring f h) (mul-Π-Ring g h))
  right-distributive-mul-add-Π-Ring =
    right-distributive-mul-add-Semiring semiring-Π-Ring

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
