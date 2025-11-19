# Commutative semirings

```agda
module commutative-algebra.commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.interchange-law
open import foundation.iterated-dependent-product-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.commutative-monoids
open import group-theory.monoids

open import ring-theory.semirings
```

</details>

## Idea

A [semiring](ring-theory.semirings.md) `A` is said to be
{{#concept "commutative" Disambiguation="semiring" Agda=is-commutative-Semiring}}
if its multiplicative operation is commutative, i.e., if `xy = yx` for all
`x, y ∈ A`.

## Definitions

### The predicate on semirings of being commutative

```agda
module _
  {l : Level} (A : Semiring l)
  where

  is-commutative-Semiring : UU l
  is-commutative-Semiring =
    (x y : type-Semiring A) → mul-Semiring A x y ＝ mul-Semiring A y x

  is-prop-is-commutative-Semiring : is-prop is-commutative-Semiring
  is-prop-is-commutative-Semiring =
    is-prop-iterated-Π 2
      ( λ x y →
        is-set-type-Semiring A (mul-Semiring A x y) (mul-Semiring A y x))

  is-commutative-prop-Semiring : Prop l
  is-commutative-prop-Semiring =
    ( is-commutative-Semiring , is-prop-is-commutative-Semiring)
```

### The type of commutative semirings

```agda
Commutative-Semiring :
  ( l : Level) → UU (lsuc l)
Commutative-Semiring l = Σ (Semiring l) is-commutative-Semiring
```

### Immediate infrastructure for commutative semirings

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  semiring-Commutative-Semiring : Semiring l
  semiring-Commutative-Semiring = pr1 A

  additive-commutative-monoid-Commutative-Semiring : Commutative-Monoid l
  additive-commutative-monoid-Commutative-Semiring =
    additive-commutative-monoid-Semiring semiring-Commutative-Semiring

  multiplicative-monoid-Commutative-Semiring : Monoid l
  multiplicative-monoid-Commutative-Semiring =
    multiplicative-monoid-Semiring semiring-Commutative-Semiring

  set-Commutative-Semiring : Set l
  set-Commutative-Semiring = set-Semiring semiring-Commutative-Semiring

  type-Commutative-Semiring : UU l
  type-Commutative-Semiring = type-Semiring semiring-Commutative-Semiring

  is-set-type-Commutative-Semiring : is-set type-Commutative-Semiring
  is-set-type-Commutative-Semiring =
    is-set-type-Semiring semiring-Commutative-Semiring

  zero-Commutative-Semiring : type-Commutative-Semiring
  zero-Commutative-Semiring = zero-Semiring semiring-Commutative-Semiring

  is-zero-Commutative-Semiring : type-Commutative-Semiring → UU l
  is-zero-Commutative-Semiring = is-zero-Semiring semiring-Commutative-Semiring

  is-zero-prop-Commutative-Semiring : type-Commutative-Semiring → Prop l
  is-zero-prop-Commutative-Semiring =
    is-zero-prop-Semiring semiring-Commutative-Semiring

  is-nonzero-Commutative-Semiring : type-Commutative-Semiring → UU l
  is-nonzero-Commutative-Semiring =
    is-nonzero-Semiring semiring-Commutative-Semiring

  add-Commutative-Semiring :
    type-Commutative-Semiring → type-Commutative-Semiring →
    type-Commutative-Semiring
  add-Commutative-Semiring = add-Semiring semiring-Commutative-Semiring

  add-Commutative-Semiring' :
    type-Commutative-Semiring → type-Commutative-Semiring →
    type-Commutative-Semiring
  add-Commutative-Semiring' = add-Semiring' semiring-Commutative-Semiring

  ap-add-Commutative-Semiring :
    {x x' y y' : type-Commutative-Semiring} →
    (x ＝ x') → (y ＝ y') →
    add-Commutative-Semiring x y ＝ add-Commutative-Semiring x' y'
  ap-add-Commutative-Semiring = ap-add-Semiring semiring-Commutative-Semiring

  associative-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( add-Commutative-Semiring (add-Commutative-Semiring x y) z) ＝
    ( add-Commutative-Semiring x (add-Commutative-Semiring y z))
  associative-add-Commutative-Semiring =
    associative-add-Semiring semiring-Commutative-Semiring

  left-unit-law-add-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    add-Commutative-Semiring zero-Commutative-Semiring x ＝ x
  left-unit-law-add-Commutative-Semiring =
    left-unit-law-add-Semiring semiring-Commutative-Semiring

  right-unit-law-add-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    add-Commutative-Semiring x zero-Commutative-Semiring ＝ x
  right-unit-law-add-Commutative-Semiring =
    right-unit-law-add-Semiring semiring-Commutative-Semiring

  commutative-add-Commutative-Semiring :
    (x y : type-Commutative-Semiring) →
    add-Commutative-Semiring x y ＝ add-Commutative-Semiring y x
  commutative-add-Commutative-Semiring =
    commutative-add-Semiring semiring-Commutative-Semiring

  interchange-add-add-Commutative-Semiring :
    (x y x' y' : type-Commutative-Semiring) →
    ( add-Commutative-Semiring
      ( add-Commutative-Semiring x y)
      ( add-Commutative-Semiring x' y')) ＝
    ( add-Commutative-Semiring
      ( add-Commutative-Semiring x x')
      ( add-Commutative-Semiring y y'))
  interchange-add-add-Commutative-Semiring =
    interchange-add-add-Semiring semiring-Commutative-Semiring

  right-swap-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( add-Commutative-Semiring (add-Commutative-Semiring x y) z) ＝
    ( add-Commutative-Semiring (add-Commutative-Semiring x z) y)
  right-swap-add-Commutative-Semiring =
    right-swap-add-Semiring semiring-Commutative-Semiring

  left-swap-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    ( add-Commutative-Semiring x (add-Commutative-Semiring y z)) ＝
    ( add-Commutative-Semiring y (add-Commutative-Semiring x z))
  left-swap-add-Commutative-Semiring =
    left-swap-add-Semiring semiring-Commutative-Semiring

  mul-Commutative-Semiring :
    (x y : type-Commutative-Semiring) → type-Commutative-Semiring
  mul-Commutative-Semiring = mul-Semiring semiring-Commutative-Semiring

  mul-Commutative-Semiring' :
    (x y : type-Commutative-Semiring) → type-Commutative-Semiring
  mul-Commutative-Semiring' = mul-Semiring' semiring-Commutative-Semiring

  ap-mul-Commutative-Semiring :
    {x x' y y' : type-Commutative-Semiring} →
    (x ＝ x') → (y ＝ y') →
    mul-Commutative-Semiring x y ＝ mul-Commutative-Semiring x' y'
  ap-mul-Commutative-Semiring = ap-mul-Semiring semiring-Commutative-Semiring

  one-Commutative-Semiring : type-Commutative-Semiring
  one-Commutative-Semiring = one-Semiring semiring-Commutative-Semiring

  left-unit-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring one-Commutative-Semiring x ＝ x
  left-unit-law-mul-Commutative-Semiring =
    left-unit-law-mul-Semiring semiring-Commutative-Semiring

  right-unit-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring x one-Commutative-Semiring ＝ x
  right-unit-law-mul-Commutative-Semiring =
    right-unit-law-mul-Semiring semiring-Commutative-Semiring

  associative-mul-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring (mul-Commutative-Semiring x y) z ＝
    mul-Commutative-Semiring x (mul-Commutative-Semiring y z)
  associative-mul-Commutative-Semiring =
    associative-mul-Semiring semiring-Commutative-Semiring

  left-distributive-mul-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring x (add-Commutative-Semiring y z) ＝
    add-Commutative-Semiring
      ( mul-Commutative-Semiring x y)
      ( mul-Commutative-Semiring x z)
  left-distributive-mul-add-Commutative-Semiring =
    left-distributive-mul-add-Semiring semiring-Commutative-Semiring

  right-distributive-mul-add-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring (add-Commutative-Semiring x y) z ＝
    add-Commutative-Semiring
      ( mul-Commutative-Semiring x z)
      ( mul-Commutative-Semiring y z)
  right-distributive-mul-add-Commutative-Semiring =
    right-distributive-mul-add-Semiring semiring-Commutative-Semiring

  commutative-mul-Commutative-Semiring :
    (x y : type-Commutative-Semiring) →
    mul-Commutative-Semiring x y ＝ mul-Commutative-Semiring y x
  commutative-mul-Commutative-Semiring = pr2 A

  multiplicative-commutative-monoid-Commutative-Semiring :
    Commutative-Monoid l
  pr1 multiplicative-commutative-monoid-Commutative-Semiring =
    multiplicative-monoid-Commutative-Semiring
  pr2 multiplicative-commutative-monoid-Commutative-Semiring =
    commutative-mul-Commutative-Semiring

  left-zero-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring zero-Commutative-Semiring x ＝
    zero-Commutative-Semiring
  left-zero-law-mul-Commutative-Semiring =
    left-zero-law-mul-Semiring semiring-Commutative-Semiring

  right-zero-law-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring) →
    mul-Commutative-Semiring x zero-Commutative-Semiring ＝
    zero-Commutative-Semiring
  right-zero-law-mul-Commutative-Semiring =
    right-zero-law-mul-Semiring semiring-Commutative-Semiring

  right-swap-mul-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring (mul-Commutative-Semiring x y) z ＝
    mul-Commutative-Semiring (mul-Commutative-Semiring x z) y
  right-swap-mul-Commutative-Semiring =
    right-swap-mul-Commutative-Monoid
      multiplicative-commutative-monoid-Commutative-Semiring

  left-swap-mul-Commutative-Semiring :
    (x y z : type-Commutative-Semiring) →
    mul-Commutative-Semiring x (mul-Commutative-Semiring y z) ＝
    mul-Commutative-Semiring y (mul-Commutative-Semiring x z)
  left-swap-mul-Commutative-Semiring =
    left-swap-mul-Commutative-Monoid
      multiplicative-commutative-monoid-Commutative-Semiring

  interchange-mul-mul-Commutative-Semiring :
    (x y x' y' : type-Commutative-Semiring) →
    ( mul-Commutative-Semiring
      ( mul-Commutative-Semiring x y)
      ( mul-Commutative-Semiring x' y')) ＝
    ( mul-Commutative-Semiring
      ( mul-Commutative-Semiring x x')
      ( mul-Commutative-Semiring y y'))
  interchange-mul-mul-Commutative-Semiring =
    interchange-law-commutative-and-associative
      ( mul-Commutative-Semiring)
      ( commutative-mul-Commutative-Semiring)
      ( associative-mul-Commutative-Semiring)
```
