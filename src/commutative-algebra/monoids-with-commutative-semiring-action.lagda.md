# Monoids with two-sided commutative semiring action

```agda
module commutative-algebra.monoids-with-commutative-semiring-action where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids

open import ring-theory.monoids-with-semiring-action
```

</details>

## Idea

Consider a [commutative semiring](commutative-algebra.commutative-semirings.md) $R$.
A {{#concept "monoid with a two-sided commutative semiring action" Agda=Monoid-With-Commutative-Semiring-Action}}
from $R$ consists of a [monoid](group-theory.monoids.md) $M$ and a binary operation $\mu : R \to M \to R \to M$ satisfying the axioms of a ring action:

1. The action distributes from the over monoid multiplication:
   $$
     r(xy)s = (rxs)(rys).
   $$
2. The action distributes from the right over addition in the commutative semiring:
   $$
     (r+s)xu = (rxu)(sxu).
   $$
3. The action distributes from the left over addition in the commutative semiring:
   $$
     rx(u+v) = (rxu)(rxv).
   $$
4. Associativity of the action
   $$
     (sr)x(uv) = s(rxu)v.
   $$
5. The unit element of the commutative semiring acts as the identity
   $$
     1x1 = x.
   $$
6. The unit element of the monoid absorbs any action
   $$
     r1u = 1.
   $$

## Definitions

### Two-sided actions of commutative semirings on monoids

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (M : Monoid l2)
  where

  action-commutative-semiring-Monoid : UU (l1 ⊔ l2)
  action-commutative-semiring-Monoid =
    action-semiring-Monoid (semiring-Commutative-Semiring R) M
```

### Monoids with commutative semiring actions

```agda
Monoid-With-Commutative-Semiring-Action :
  {l1 : Level} (l2 : Level) (R : Commutative-Semiring l1) → UU (l1 ⊔ lsuc l2)
Monoid-With-Commutative-Semiring-Action l2 R =
  Monoid-With-Semiring-Action l2 (semiring-Commutative-Semiring R)

module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (M : Monoid-With-Commutative-Semiring-Action l2 R)
  where

  monoid-Monoid-With-Commutative-Semiring-Action :
    Monoid l2
  monoid-Monoid-With-Commutative-Semiring-Action =
    monoid-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  set-Monoid-With-Commutative-Semiring-Action :
    Set l2
  set-Monoid-With-Commutative-Semiring-Action =
    set-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  type-Monoid-With-Commutative-Semiring-Action :
    UU l2
  type-Monoid-With-Commutative-Semiring-Action =
    type-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  is-set-type-Monoid-With-Commutative-Semiring-Action :
    is-set type-Monoid-With-Commutative-Semiring-Action
  is-set-type-Monoid-With-Commutative-Semiring-Action =
    is-set-type-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  mul-Monoid-With-Commutative-Semiring-Action :
    (x y : type-Monoid-With-Commutative-Semiring-Action) →
    type-Monoid-With-Commutative-Semiring-Action
  mul-Monoid-With-Commutative-Semiring-Action =
    mul-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  mul-Monoid-With-Commutative-Semiring-Action' :
    (x y : type-Monoid-With-Commutative-Semiring-Action) →
    type-Monoid-With-Commutative-Semiring-Action
  mul-Monoid-With-Commutative-Semiring-Action' =
    mul-Monoid-With-Semiring-Action'
      ( semiring-Commutative-Semiring R)
      ( M)

  associative-mul-Monoid-With-Commutative-Semiring-Action :
    (x y z : type-Monoid-With-Commutative-Semiring-Action) →
    mul-Monoid-With-Commutative-Semiring-Action
      ( mul-Monoid-With-Commutative-Semiring-Action x y) z ＝
    mul-Monoid-With-Commutative-Semiring-Action x
      ( mul-Monoid-With-Commutative-Semiring-Action y z)
  associative-mul-Monoid-With-Commutative-Semiring-Action =
    associative-mul-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  unit-Monoid-With-Commutative-Semiring-Action :
    type-Monoid-With-Commutative-Semiring-Action
  unit-Monoid-With-Commutative-Semiring-Action =
    unit-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  is-unit-Monoid-With-Commutative-Semiring-Action :
    type-Monoid-With-Commutative-Semiring-Action → UU l2
  is-unit-Monoid-With-Commutative-Semiring-Action =
    is-unit-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  left-unit-law-mul-Monoid-With-Commutative-Semiring-Action :
    (x : type-Monoid-With-Commutative-Semiring-Action) →
    mul-Monoid-With-Commutative-Semiring-Action
      ( unit-Monoid-With-Commutative-Semiring-Action)
      ( x) ＝
    x
  left-unit-law-mul-Monoid-With-Commutative-Semiring-Action =
    left-unit-law-mul-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  right-unit-law-mul-Monoid-With-Commutative-Semiring-Action :
    (x : type-Monoid-With-Commutative-Semiring-Action) →
    mul-Monoid-With-Commutative-Semiring-Action
      ( x)
      ( unit-Monoid-With-Commutative-Semiring-Action) ＝
    ( x)
  right-unit-law-mul-Monoid-With-Commutative-Semiring-Action =
    right-unit-law-mul-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  action-Monoid-With-Commutative-Semiring-Action :
    type-Commutative-Semiring R →
    type-Monoid-With-Commutative-Semiring-Action →
    type-Commutative-Semiring R →
    type-Monoid-With-Commutative-Semiring-Action
  action-Monoid-With-Commutative-Semiring-Action =
    action-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  distributive-action-mul-Monoid-With-Commutative-Semiring-Action :
    (r : type-Commutative-Semiring R)
    (x y : type-Monoid-With-Commutative-Semiring-Action)
    (u : type-Commutative-Semiring R) →
    action-Monoid-With-Commutative-Semiring-Action
      ( r)
      ( mul-Monoid-With-Commutative-Semiring-Action x y)
      ( u) ＝
    mul-Monoid-With-Commutative-Semiring-Action
      ( action-Monoid-With-Commutative-Semiring-Action r x u)
      ( action-Monoid-With-Commutative-Semiring-Action r y u)
  distributive-action-mul-Monoid-With-Commutative-Semiring-Action =
    distributive-action-mul-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  right-distributive-action-add-Monoid-With-Commutative-Semiring-Action :
    (r s : type-Commutative-Semiring R)
    (x : type-Monoid-With-Commutative-Semiring-Action)
    (u : type-Commutative-Semiring R) →
    action-Monoid-With-Commutative-Semiring-Action
      ( add-Commutative-Semiring R r s) x u ＝
    mul-Monoid-With-Commutative-Semiring-Action
      ( action-Monoid-With-Commutative-Semiring-Action r x u)
      ( action-Monoid-With-Commutative-Semiring-Action s x u)
  right-distributive-action-add-Monoid-With-Commutative-Semiring-Action =
    right-distributive-action-add-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  left-distributive-action-add-Monoid-With-Commutative-Semiring-Action :
    (r : type-Commutative-Semiring R)
    (x : type-Monoid-With-Commutative-Semiring-Action)
    (u v : type-Commutative-Semiring R) →
    action-Monoid-With-Commutative-Semiring-Action r x
      ( add-Commutative-Semiring R u v) ＝
    mul-Monoid-With-Commutative-Semiring-Action
      ( action-Monoid-With-Commutative-Semiring-Action r x u)
      ( action-Monoid-With-Commutative-Semiring-Action r x v)
  left-distributive-action-add-Monoid-With-Commutative-Semiring-Action =
    left-distributive-action-add-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  associative-action-Monoid-With-Commutative-Semiring-Action :
    (s r : type-Commutative-Semiring R)
    (x : type-Monoid-With-Commutative-Semiring-Action)
    (u v : type-Commutative-Semiring R) →
    action-Monoid-With-Commutative-Semiring-Action
      ( mul-Commutative-Semiring R s r)
      ( x)
      ( mul-Commutative-Semiring R u v) ＝
    action-Monoid-With-Commutative-Semiring-Action
      ( s)
      ( action-Monoid-With-Commutative-Semiring-Action r x u)
      ( v)
  associative-action-Monoid-With-Commutative-Semiring-Action =
    associative-action-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  unit-law-action-Monoid-With-Commutative-Semiring-Action :
    (x : type-Monoid-With-Commutative-Semiring-Action) →
    action-Monoid-With-Commutative-Semiring-Action
      ( one-Commutative-Semiring R) x (one-Commutative-Semiring R) ＝ x
  unit-law-action-Monoid-With-Commutative-Semiring-Action =
    unit-law-action-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)

  absorption-law-action-Monoid-With-Commutative-Semiring-Action :
    (r u : type-Commutative-Semiring R) →
    action-Monoid-With-Commutative-Semiring-Action
      ( r)
      ( unit-Monoid-With-Commutative-Semiring-Action)
      ( u) ＝
    unit-Monoid-With-Commutative-Semiring-Action
  absorption-law-action-Monoid-With-Commutative-Semiring-Action =
    absorption-law-action-Monoid-With-Semiring-Action
      ( semiring-Commutative-Semiring R)
      ( M)
```

## Properties

### The underlying additive monoid of a commutative semiring is a monoid with a left commutative semiring action

```agda
module _
  {l1 : Level} (R : Commutative-Semiring l1)
  where

  two-sided-mul-Commutative-Semiring :
    (r x u : type-Commutative-Semiring R) → type-Commutative-Semiring R
  two-sided-mul-Commutative-Semiring =
    two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  distributive-two-sided-mul-Commutative-Semiring :
    (r x y u : type-Commutative-Semiring R) →
    two-sided-mul-Commutative-Semiring
      ( r)
      ( add-Commutative-Semiring R x y)
      ( u) ＝
    add-Commutative-Semiring R
      ( two-sided-mul-Commutative-Semiring r x u)
      ( two-sided-mul-Commutative-Semiring r y u)
  distributive-two-sided-mul-Commutative-Semiring
    =
    distributive-two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  right-distributive-two-sided-mul-Commutative-Semiring :
    (r s x u : type-Commutative-Semiring R) →
    two-sided-mul-Commutative-Semiring
      ( add-Commutative-Semiring R r s)
      ( x)
      ( u) ＝
    add-Commutative-Semiring R
      ( two-sided-mul-Commutative-Semiring r x u)
      ( two-sided-mul-Commutative-Semiring s x u)
  right-distributive-two-sided-mul-Commutative-Semiring
    =
    right-distributive-two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  left-distributive-two-sided-mul-Commutative-Semiring :
    (r x u v : type-Commutative-Semiring R) →
    two-sided-mul-Commutative-Semiring r x
      ( add-Commutative-Semiring R u v) ＝
    add-Commutative-Semiring R
      ( two-sided-mul-Commutative-Semiring r x u)
      ( two-sided-mul-Commutative-Semiring r x v)
  left-distributive-two-sided-mul-Commutative-Semiring
    =
    left-distributive-two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  associative-two-sided-mul-Commutative-Semiring :
    (s r x u v : type-Commutative-Semiring R) →
    two-sided-mul-Commutative-Semiring
      ( mul-Commutative-Semiring R s r)
      ( x)
      ( mul-Commutative-Semiring R u v) ＝
    two-sided-mul-Commutative-Semiring
      ( s)
      ( two-sided-mul-Commutative-Semiring r x u)
      ( v)
  associative-two-sided-mul-Commutative-Semiring =
    associative-two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  unit-law-two-sided-mul-Commutative-Semiring :
    (x : type-Commutative-Semiring R) →
    two-sided-mul-Commutative-Semiring
      ( one-Commutative-Semiring R)
      ( x)
      ( one-Commutative-Semiring R) ＝
    x
  unit-law-two-sided-mul-Commutative-Semiring =
    unit-law-two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  absorption-law-two-sided-mul-Commutative-Semiring :
    (r u : type-Commutative-Semiring R) →
    two-sided-mul-Commutative-Semiring
      ( r)
      ( zero-Commutative-Semiring R)
      ( u) ＝
    zero-Commutative-Semiring R
  absorption-law-two-sided-mul-Commutative-Semiring =
    absorption-law-two-sided-mul-Semiring
      ( semiring-Commutative-Semiring R)

  additive-monoid-with-semiring-action-Commutative-Semiring :
    Monoid-With-Commutative-Semiring-Action l1 R
  additive-monoid-with-semiring-action-Commutative-Semiring =
    additive-monoid-with-semiring-action-Semiring
      ( semiring-Commutative-Semiring R)
```
