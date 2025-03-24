# Dependent products of commutative semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module commutative-algebra.dependent-products-commutative-semirings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings funext univalence truncations

open import foundation.dependent-pair-types
open import foundation.identity-types funext
open import foundation.sets funext univalence
open import foundation.universe-levels

open import group-theory.commutative-monoids funext univalence truncations
open import group-theory.dependent-products-commutative-monoids funext univalence truncations

open import ring-theory.dependent-products-semirings funext univalence truncations
open import ring-theory.semirings funext univalence truncations
```

</details>

## Idea

Given a family of commutative semirings `A i` indexed by `i : I`, their
**dependent product** `Π (i:I), A i` is again a commutative semiring.

## Definition

```agda
module _
  {l1 l2 : Level} (I : UU l1) (A : I → Commutative-Semiring l2)
  where

  semiring-Π-Commutative-Semiring : Semiring (l1 ⊔ l2)
  semiring-Π-Commutative-Semiring =
    Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  additive-commutative-monoid-Π-Commutative-Semiring :
    Commutative-Monoid (l1 ⊔ l2)
  additive-commutative-monoid-Π-Commutative-Semiring =
    Π-Commutative-Monoid I
      ( λ i → additive-commutative-monoid-Commutative-Semiring (A i))

  multiplicative-commutative-monoid-Π-Commutative-Semiring :
    Commutative-Monoid (l1 ⊔ l2)
  multiplicative-commutative-monoid-Π-Commutative-Semiring =
    Π-Commutative-Monoid I
      ( λ i → multiplicative-commutative-monoid-Commutative-Semiring (A i))

  set-Π-Commutative-Semiring : Set (l1 ⊔ l2)
  set-Π-Commutative-Semiring =
    set-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  type-Π-Commutative-Semiring : UU (l1 ⊔ l2)
  type-Π-Commutative-Semiring =
    type-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  is-set-type-Π-Commutative-Semiring : is-set type-Π-Commutative-Semiring
  is-set-type-Π-Commutative-Semiring =
    is-set-type-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  add-Π-Commutative-Semiring :
    type-Π-Commutative-Semiring → type-Π-Commutative-Semiring →
    type-Π-Commutative-Semiring
  add-Π-Commutative-Semiring =
    add-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  zero-Π-Commutative-Semiring : type-Π-Commutative-Semiring
  zero-Π-Commutative-Semiring =
    zero-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  associative-add-Π-Commutative-Semiring :
    (x y z : type-Π-Commutative-Semiring) →
    add-Π-Commutative-Semiring (add-Π-Commutative-Semiring x y) z ＝
    add-Π-Commutative-Semiring x (add-Π-Commutative-Semiring y z)
  associative-add-Π-Commutative-Semiring =
    associative-add-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  left-unit-law-add-Π-Commutative-Semiring :
    (x : type-Π-Commutative-Semiring) →
    add-Π-Commutative-Semiring zero-Π-Commutative-Semiring x ＝ x
  left-unit-law-add-Π-Commutative-Semiring =
    left-unit-law-add-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  right-unit-law-add-Π-Commutative-Semiring :
    (x : type-Π-Commutative-Semiring) →
    add-Π-Commutative-Semiring x zero-Π-Commutative-Semiring ＝ x
  right-unit-law-add-Π-Commutative-Semiring =
    right-unit-law-add-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  commutative-add-Π-Commutative-Semiring :
    (x y : type-Π-Commutative-Semiring) →
    add-Π-Commutative-Semiring x y ＝ add-Π-Commutative-Semiring y x
  commutative-add-Π-Commutative-Semiring =
    commutative-add-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  mul-Π-Commutative-Semiring :
    type-Π-Commutative-Semiring → type-Π-Commutative-Semiring →
    type-Π-Commutative-Semiring
  mul-Π-Commutative-Semiring =
    mul-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  one-Π-Commutative-Semiring : type-Π-Commutative-Semiring
  one-Π-Commutative-Semiring =
    one-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  associative-mul-Π-Commutative-Semiring :
    (x y z : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring (mul-Π-Commutative-Semiring x y) z ＝
    mul-Π-Commutative-Semiring x (mul-Π-Commutative-Semiring y z)
  associative-mul-Π-Commutative-Semiring =
    associative-mul-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  left-unit-law-mul-Π-Commutative-Semiring :
    (x : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring one-Π-Commutative-Semiring x ＝ x
  left-unit-law-mul-Π-Commutative-Semiring =
    left-unit-law-mul-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  right-unit-law-mul-Π-Commutative-Semiring :
    (x : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring x one-Π-Commutative-Semiring ＝ x
  right-unit-law-mul-Π-Commutative-Semiring =
    right-unit-law-mul-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  left-distributive-mul-add-Π-Commutative-Semiring :
    (f g h : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring f (add-Π-Commutative-Semiring g h) ＝
    add-Π-Commutative-Semiring
      ( mul-Π-Commutative-Semiring f g)
      ( mul-Π-Commutative-Semiring f h)
  left-distributive-mul-add-Π-Commutative-Semiring =
    left-distributive-mul-add-Π-Semiring I
      ( λ i → semiring-Commutative-Semiring (A i))

  right-distributive-mul-add-Π-Commutative-Semiring :
    (f g h : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring (add-Π-Commutative-Semiring f g) h ＝
    add-Π-Commutative-Semiring
      ( mul-Π-Commutative-Semiring f h)
      ( mul-Π-Commutative-Semiring g h)
  right-distributive-mul-add-Π-Commutative-Semiring =
    right-distributive-mul-add-Π-Semiring I
      ( λ i → semiring-Commutative-Semiring (A i))

  left-zero-law-mul-Π-Commutative-Semiring :
    (f : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring zero-Π-Commutative-Semiring f ＝
    zero-Π-Commutative-Semiring
  left-zero-law-mul-Π-Commutative-Semiring =
    left-zero-law-mul-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  right-zero-law-mul-Π-Commutative-Semiring :
    (f : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring f zero-Π-Commutative-Semiring ＝
    zero-Π-Commutative-Semiring
  right-zero-law-mul-Π-Commutative-Semiring =
    right-zero-law-mul-Π-Semiring I (λ i → semiring-Commutative-Semiring (A i))

  commutative-mul-Π-Commutative-Semiring :
    (f g : type-Π-Commutative-Semiring) →
    mul-Π-Commutative-Semiring f g ＝ mul-Π-Commutative-Semiring g f
  commutative-mul-Π-Commutative-Semiring =
    commutative-mul-Commutative-Monoid
      multiplicative-commutative-monoid-Π-Commutative-Semiring

  Π-Commutative-Semiring : Commutative-Semiring (l1 ⊔ l2)
  pr1 Π-Commutative-Semiring = semiring-Π-Commutative-Semiring
  pr2 Π-Commutative-Semiring = commutative-mul-Π-Commutative-Semiring
```
