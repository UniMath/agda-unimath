# Monoids with two-sided semiring action

```agda
module ring-theory.monoids-with-semiring-action where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.monoids

open import ring-theory.semirings
```

</details>

## Idea

Consider a [semiring](ring-theory.semirings.md) $R$.
A {{#concept "monoid with a two-sided semiring action" Agda=Monoid-With-Semiring-Action}}
from $R$ consists of a [monoid](group-theory.monoids.md) $M$ and a binary operation $\mu : R \to M \to R \to M$ satisfying the axioms of a ring action:

1. The action distributes from the over monoid multiplication:
   $$
     r(xy)s = (rxs)(rys).
   $$
2. The action distributes from the right over addition in the semiring:
   $$
     (r+s)xu = (rxu)(sxu).
   $$
3. The action distributes from the left over addition in the semiring:
   $$
     rx(u+v) = (rxu)(rxv).
   $$
4. Associativity of the action
   $$
     (sr)x(uv) = s(rxu)v.
   $$
5. The unit element of the semiring acts as the identity
   $$
     1x1 = x.
   $$
6. The unit element of the monoid absorbs any action
   $$
     r1u = 1.
   $$

## Definitions

### Two-sided actions of semirings on monoids

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid l2)
  where

  action-semiring-Monoid : UU (l1 ⊔ l2)
  action-semiring-Monoid =
    Σ ( type-Semiring R → type-Monoid M → type-Semiring R → type-Monoid M)
      ( λ μ →
        ( (r : type-Semiring R) (x y : type-Monoid M) (u : type-Semiring R) →
          μ r (mul-Monoid M x y) u ＝ mul-Monoid M (μ r x u) (μ r y u)) ×
        ( (r s : type-Semiring R) (x : type-Monoid M) (u : type-Semiring R) →
          μ (add-Semiring R r s) x u ＝ mul-Monoid M (μ r x u) (μ s x u)) ×
        ( (r : type-Semiring R) (x : type-Monoid M) (u v : type-Semiring R) →
          μ r x (add-Semiring R u v) ＝ mul-Monoid M (μ r x u) (μ r x v)) ×
        ( (s r : type-Semiring R) (x : type-Monoid M) (u v : type-Semiring R) →
          μ (mul-Semiring R s r) x (mul-Semiring R u v) ＝ μ s (μ r x u) v) ×
        ( (x : type-Monoid M) → μ (one-Semiring R) x (one-Semiring R) ＝ x) ×
        ( (r u : type-Semiring R) → μ r (unit-Monoid M) u ＝ unit-Monoid M))
```

### Monoids with semiring actions

```agda
Monoid-With-Semiring-Action :
  {l1 : Level} (l2 : Level) (R : Semiring l1) → UU (l1 ⊔ lsuc l2)
Monoid-With-Semiring-Action l2 R =
  Σ ( Monoid l2) (action-semiring-Monoid R)

module _
  {l1 l2 : Level} (R : Semiring l1) (M : Monoid-With-Semiring-Action l2 R)
  where

  monoid-Monoid-With-Semiring-Action :
    Monoid l2
  monoid-Monoid-With-Semiring-Action =
    pr1 M

  set-Monoid-With-Semiring-Action :
    Set l2
  set-Monoid-With-Semiring-Action =
    set-Monoid monoid-Monoid-With-Semiring-Action

  type-Monoid-With-Semiring-Action :
    UU l2
  type-Monoid-With-Semiring-Action =
    type-Monoid monoid-Monoid-With-Semiring-Action

  is-set-type-Monoid-With-Semiring-Action :
    is-set type-Monoid-With-Semiring-Action
  is-set-type-Monoid-With-Semiring-Action =
    is-set-type-Monoid monoid-Monoid-With-Semiring-Action

  mul-Monoid-With-Semiring-Action :
    (x y : type-Monoid-With-Semiring-Action) →
    type-Monoid-With-Semiring-Action
  mul-Monoid-With-Semiring-Action =
    mul-Monoid monoid-Monoid-With-Semiring-Action

  mul-Monoid-With-Semiring-Action' :
    (x y : type-Monoid-With-Semiring-Action) →
    type-Monoid-With-Semiring-Action
  mul-Monoid-With-Semiring-Action' =
    mul-Monoid' monoid-Monoid-With-Semiring-Action

  associative-mul-Monoid-With-Semiring-Action :
    (x y z : type-Monoid-With-Semiring-Action) →
    mul-Monoid-With-Semiring-Action (mul-Monoid-With-Semiring-Action x y) z ＝
    mul-Monoid-With-Semiring-Action x (mul-Monoid-With-Semiring-Action y z)
  associative-mul-Monoid-With-Semiring-Action =
    associative-mul-Monoid monoid-Monoid-With-Semiring-Action

  unit-Monoid-With-Semiring-Action :
    type-Monoid-With-Semiring-Action
  unit-Monoid-With-Semiring-Action =
    unit-Monoid monoid-Monoid-With-Semiring-Action

  is-unit-Monoid-With-Semiring-Action :
    type-Monoid-With-Semiring-Action → UU l2
  is-unit-Monoid-With-Semiring-Action =
    is-unit-Monoid monoid-Monoid-With-Semiring-Action

  left-unit-law-mul-Monoid-With-Semiring-Action :
    (x : type-Monoid-With-Semiring-Action) →
    mul-Monoid-With-Semiring-Action
      ( unit-Monoid-With-Semiring-Action)
      ( x) ＝
    x
  left-unit-law-mul-Monoid-With-Semiring-Action =
    left-unit-law-mul-Monoid monoid-Monoid-With-Semiring-Action

  right-unit-law-mul-Monoid-With-Semiring-Action :
    (x : type-Monoid-With-Semiring-Action) →
    mul-Monoid-With-Semiring-Action
      ( x)
      ( unit-Monoid-With-Semiring-Action) ＝
    ( x)
  right-unit-law-mul-Monoid-With-Semiring-Action =
    right-unit-law-mul-Monoid monoid-Monoid-With-Semiring-Action

  action-Monoid-With-Semiring-Action :
    type-Semiring R → type-Monoid-With-Semiring-Action → type-Semiring R →
    type-Monoid-With-Semiring-Action
  action-Monoid-With-Semiring-Action =
    pr1 (pr2 M)

  distributive-action-mul-Monoid-With-Semiring-Action :
    (r : type-Semiring R) (x y : type-Monoid-With-Semiring-Action)
    (u : type-Semiring R) →
    action-Monoid-With-Semiring-Action
      ( r)
      ( mul-Monoid-With-Semiring-Action x y)
      ( u) ＝
    mul-Monoid-With-Semiring-Action
      ( action-Monoid-With-Semiring-Action r x u)
      ( action-Monoid-With-Semiring-Action r y u)
  distributive-action-mul-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 M))

  right-distributive-action-add-Monoid-With-Semiring-Action :
    (r s : type-Semiring R) (x : type-Monoid-With-Semiring-Action)
    (u : type-Semiring R) →
    action-Monoid-With-Semiring-Action (add-Semiring R r s) x u ＝
    mul-Monoid-With-Semiring-Action
      ( action-Monoid-With-Semiring-Action r x u)
      ( action-Monoid-With-Semiring-Action s x u)
  right-distributive-action-add-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 M)))

  left-distributive-action-add-Monoid-With-Semiring-Action :
    (r : type-Semiring R) (x : type-Monoid-With-Semiring-Action)
    (u v : type-Semiring R) →
    action-Monoid-With-Semiring-Action r x (add-Semiring R u v) ＝
    mul-Monoid-With-Semiring-Action
      ( action-Monoid-With-Semiring-Action r x u)
      ( action-Monoid-With-Semiring-Action r x v)
  left-distributive-action-add-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 M))))

  associative-action-Monoid-With-Semiring-Action :
    (s r : type-Semiring R) (x : type-Monoid-With-Semiring-Action)
    (u v : type-Semiring R) →
    action-Monoid-With-Semiring-Action
      ( mul-Semiring R s r)
      ( x)
      ( mul-Semiring R u v) ＝
    action-Monoid-With-Semiring-Action
      ( s)
      ( action-Monoid-With-Semiring-Action r x u)
      ( v)
  associative-action-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 M)))))

  unit-law-action-Monoid-With-Semiring-Action :
    (x : type-Monoid-With-Semiring-Action) →
    action-Monoid-With-Semiring-Action (one-Semiring R) x (one-Semiring R) ＝ x
  unit-law-action-Monoid-With-Semiring-Action =
    pr1 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))

  absorption-law-action-Monoid-With-Semiring-Action :
    (r u : type-Semiring R) →
    action-Monoid-With-Semiring-Action
      ( r)
      ( unit-Monoid-With-Semiring-Action)
      ( u) ＝
    unit-Monoid-With-Semiring-Action
  absorption-law-action-Monoid-With-Semiring-Action =
    pr2 (pr2 (pr2 (pr2 (pr2 (pr2 (pr2 M))))))
```

## Properties

### The underlying additive monoid of a semiring is a monoid with a left semiring action

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  action-additive-monoid-with-semiring-action-Semiring :
    (r x u : type-Semiring R) → type-Semiring R
  action-additive-monoid-with-semiring-action-Semiring r x u =
    mul-Semiring R (mul-Semiring R r x) u

  distributive-action-additive-monoid-with-semiring-action-Semiring :
    (r x y u : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( r)
      ( add-Semiring R x y)
      ( u) ＝
    add-Semiring R
      ( action-additive-monoid-with-semiring-action-Semiring r x u)
      ( action-additive-monoid-with-semiring-action-Semiring r y u)
  distributive-action-additive-monoid-with-semiring-action-Semiring r x y u =
    ap (mul-Semiring' R u) (left-distributive-mul-add-Semiring R r x y) ∙
    right-distributive-mul-add-Semiring R
      ( mul-Semiring R r x)
      ( mul-Semiring R r y)
      ( u)

  right-distributive-action-additive-monoid-with-semiring-action-Semiring :
    (r s x u : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( add-Semiring R r s)
      ( x)
      ( u) ＝
    add-Semiring R
      ( action-additive-monoid-with-semiring-action-Semiring r x u)
      ( action-additive-monoid-with-semiring-action-Semiring s x u)
  right-distributive-action-additive-monoid-with-semiring-action-Semiring
    r s x u =
    ap (mul-Semiring' R u) (right-distributive-mul-add-Semiring R r s x) ∙
    right-distributive-mul-add-Semiring R
      ( mul-Semiring R r x)
      ( mul-Semiring R s x)
      ( u)

  left-distributive-action-additive-monoid-with-semiring-action-Semiring :
    (r x u v : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring r x
      ( add-Semiring R u v) ＝
    add-Semiring R
      ( action-additive-monoid-with-semiring-action-Semiring r x u)
      ( action-additive-monoid-with-semiring-action-Semiring r x v)
  left-distributive-action-additive-monoid-with-semiring-action-Semiring
    r x u v =
    left-distributive-mul-add-Semiring R (mul-Semiring R r x) u v

  associative-action-additive-monoid-with-semiring-action-Semiring :
    (s r x u v : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( mul-Semiring R s r)
      ( x)
      ( mul-Semiring R u v) ＝
    action-additive-monoid-with-semiring-action-Semiring
      ( s)
      ( action-additive-monoid-with-semiring-action-Semiring r x u)
      ( v)
  associative-action-additive-monoid-with-semiring-action-Semiring s r x u v =
    ( inv-associative-mul-Semiring R _ _ _) ∙
    ( ap
      ( mul-Semiring' R v)
      ( ( ap (mul-Semiring' R u) (associative-mul-Semiring R s r x)) ∙
        ( associative-mul-Semiring R s (mul-Semiring R r x) u)))

  unit-law-action-additive-monoid-with-semiring-action-Semiring :
    (x : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( one-Semiring R)
      ( x)
      ( one-Semiring R) ＝
    x
  unit-law-action-additive-monoid-with-semiring-action-Semiring x =
    right-unit-law-mul-Semiring R _ ∙ left-unit-law-mul-Semiring R _

  absorption-law-action-additive-monoid-with-semiring-action-Semiring :
    (r u : type-Semiring R) →
    action-additive-monoid-with-semiring-action-Semiring
      ( r)
      ( zero-Semiring R)
      ( u) ＝
    zero-Semiring R
  absorption-law-action-additive-monoid-with-semiring-action-Semiring r u =
    ap (mul-Semiring' R u) (right-zero-law-mul-Semiring R r) ∙
    left-zero-law-mul-Semiring R u

  additive-monoid-with-semiring-action-Semiring :
    Monoid-With-Semiring-Action l1 R
  additive-monoid-with-semiring-action-Semiring =
    ( additive-monoid-Semiring R ,
      action-additive-monoid-with-semiring-action-Semiring ,
      distributive-action-additive-monoid-with-semiring-action-Semiring ,
      right-distributive-action-additive-monoid-with-semiring-action-Semiring ,
      left-distributive-action-additive-monoid-with-semiring-action-Semiring ,
      associative-action-additive-monoid-with-semiring-action-Semiring ,
      unit-law-action-additive-monoid-with-semiring-action-Semiring ,
      absorption-law-action-additive-monoid-with-semiring-action-Semiring)
```
