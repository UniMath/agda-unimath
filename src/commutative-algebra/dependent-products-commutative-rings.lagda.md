# Dependent products of commutative rings

```agda
module commutative-algebra.dependent-products-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.commutative-monoids
open import group-theory.dependent-products-commutative-monoids

open import ring-theory.dependent-products-rings
open import ring-theory.rings
```

</details>

## Idea

Given a family of commutative rings `A i` indexed by `i : I`, their **dependent
product** `Π(i:I), A i` is again a commutative ring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A : I → Commutative-Ring l2)
  where

  ring-Π-Commutative-Ring : Ring (l1 ⊔ l2)
  ring-Π-Commutative-Ring = Π-Ring I (λ i → ring-Commutative-Ring (A i))

  ab-Π-Commutative-Ring : Ab (l1 ⊔ l2)
  ab-Π-Commutative-Ring = ab-Ring ring-Π-Commutative-Ring

  multiplicative-commutative-monoid-Π-Commutative-Ring :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-Π-Commutative-Ring =
    Π-Commutative-Monoid I
      ( λ i → multiplicative-commutative-monoid-Commutative-Ring (A i))

  set-Π-Commutative-Ring : Set (l1 ⊔ l2)
  set-Π-Commutative-Ring = set-Ring ring-Π-Commutative-Ring

  type-Π-Commutative-Ring : UU (l1 ⊔ l2)
  type-Π-Commutative-Ring = type-Ring ring-Π-Commutative-Ring

  is-set-type-Π-Commutative-Ring : is-set type-Π-Commutative-Ring
  is-set-type-Π-Commutative-Ring =
    is-set-type-Ring ring-Π-Commutative-Ring

  add-Π-Commutative-Ring :
    type-Π-Commutative-Ring → type-Π-Commutative-Ring →
    type-Π-Commutative-Ring
  add-Π-Commutative-Ring = add-Ring ring-Π-Commutative-Ring

  zero-Π-Commutative-Ring : type-Π-Commutative-Ring
  zero-Π-Commutative-Ring = zero-Ring ring-Π-Commutative-Ring

  associative-add-Π-Commutative-Ring :
    (x y z : type-Π-Commutative-Ring) →
    add-Π-Commutative-Ring (add-Π-Commutative-Ring x y) z ＝
    add-Π-Commutative-Ring x (add-Π-Commutative-Ring y z)
  associative-add-Π-Commutative-Ring =
    associative-add-Ring ring-Π-Commutative-Ring

  left-unit-law-add-Π-Commutative-Ring :
    (x : type-Π-Commutative-Ring) →
    add-Π-Commutative-Ring zero-Π-Commutative-Ring x ＝ x
  left-unit-law-add-Π-Commutative-Ring =
    left-unit-law-add-Ring ring-Π-Commutative-Ring

  right-unit-law-add-Π-Commutative-Ring :
    (x : type-Π-Commutative-Ring) →
    add-Π-Commutative-Ring x zero-Π-Commutative-Ring ＝ x
  right-unit-law-add-Π-Commutative-Ring =
    right-unit-law-add-Ring ring-Π-Commutative-Ring

  commutative-add-Π-Commutative-Ring :
    (x y : type-Π-Commutative-Ring) →
    add-Π-Commutative-Ring x y ＝ add-Π-Commutative-Ring y x
  commutative-add-Π-Commutative-Ring =
    commutative-add-Ring ring-Π-Commutative-Ring

  mul-Π-Commutative-Ring :
    type-Π-Commutative-Ring → type-Π-Commutative-Ring →
    type-Π-Commutative-Ring
  mul-Π-Commutative-Ring =
    mul-Ring ring-Π-Commutative-Ring

  one-Π-Commutative-Ring : type-Π-Commutative-Ring
  one-Π-Commutative-Ring =
    one-Ring ring-Π-Commutative-Ring

  associative-mul-Π-Commutative-Ring :
    (x y z : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring (mul-Π-Commutative-Ring x y) z ＝
    mul-Π-Commutative-Ring x (mul-Π-Commutative-Ring y z)
  associative-mul-Π-Commutative-Ring =
    associative-mul-Ring ring-Π-Commutative-Ring

  left-unit-law-mul-Π-Commutative-Ring :
    (x : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring one-Π-Commutative-Ring x ＝ x
  left-unit-law-mul-Π-Commutative-Ring =
    left-unit-law-mul-Ring ring-Π-Commutative-Ring

  right-unit-law-mul-Π-Commutative-Ring :
    (x : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring x one-Π-Commutative-Ring ＝ x
  right-unit-law-mul-Π-Commutative-Ring =
    right-unit-law-mul-Ring ring-Π-Commutative-Ring

  left-distributive-mul-add-Π-Commutative-Ring :
    (f g h : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring f (add-Π-Commutative-Ring g h) ＝
    add-Π-Commutative-Ring
      ( mul-Π-Commutative-Ring f g)
      ( mul-Π-Commutative-Ring f h)
  left-distributive-mul-add-Π-Commutative-Ring =
    left-distributive-mul-add-Ring ring-Π-Commutative-Ring

  right-distributive-mul-add-Π-Commutative-Ring :
    (f g h : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring (add-Π-Commutative-Ring f g) h ＝
    add-Π-Commutative-Ring
      ( mul-Π-Commutative-Ring f h)
      ( mul-Π-Commutative-Ring g h)
  right-distributive-mul-add-Π-Commutative-Ring =
    right-distributive-mul-add-Ring ring-Π-Commutative-Ring

  left-zero-law-mul-Π-Commutative-Ring :
    (f : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring zero-Π-Commutative-Ring f ＝
    zero-Π-Commutative-Ring
  left-zero-law-mul-Π-Commutative-Ring =
    left-zero-law-mul-Ring ring-Π-Commutative-Ring

  right-zero-law-mul-Π-Commutative-Ring :
    (f : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring f zero-Π-Commutative-Ring ＝
    zero-Π-Commutative-Ring
  right-zero-law-mul-Π-Commutative-Ring =
    right-zero-law-mul-Ring ring-Π-Commutative-Ring

  commutative-mul-Π-Commutative-Ring :
    (f g : type-Π-Commutative-Ring) →
    mul-Π-Commutative-Ring f g ＝ mul-Π-Commutative-Ring g f
  commutative-mul-Π-Commutative-Ring =
    commutative-mul-Commutative-Monoid
      multiplicative-commutative-monoid-Π-Commutative-Ring

  Π-Commutative-Ring : Commutative-Ring (l1 ⊔ l2)
  pr1 Π-Commutative-Ring = ring-Π-Commutative-Ring
  pr2 Π-Commutative-Ring = commutative-mul-Π-Commutative-Ring
```
