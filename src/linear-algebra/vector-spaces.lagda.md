# Vector spaces

```agda
module linear-algebra.vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.local-commutative-rings

open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.left-modules-commutative-rings
```

</details>

## Idea

A {{#concept "vector space" WD="vector space" WDID=Q125977}} is a
[left module](linear-algebra.left-modules-rings.md) over a
[local commutative ring](commutative-algebra.local-commutative-rings.md).

## Definition

```agda
Vector-Space :
  {l1 : Level} (l2 : Level) → Local-Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
Vector-Space l2 R =
  left-module-Commutative-Ring l2 (commutative-ring-Local-Commutative-Ring R)
```

## Properties

```agda
module _
  {l1 l2 : Level} (R : Local-Commutative-Ring l1) (V : Vector-Space l2 R)
  where

  ab-Vector-Space : Ab l2
  ab-Vector-Space =
    ab-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  set-Vector-Space : Set l2
  set-Vector-Space = set-Ab ab-Vector-Space

  type-Vector-Space : UU l2
  type-Vector-Space = type-Ab ab-Vector-Space

  add-Vector-Space : type-Vector-Space → type-Vector-Space → type-Vector-Space
  add-Vector-Space = add-Ab ab-Vector-Space

  zero-Vector-Space : type-Vector-Space
  zero-Vector-Space = zero-Ab ab-Vector-Space

  neg-Vector-Space : type-Vector-Space → type-Vector-Space
  neg-Vector-Space = neg-Ab ab-Vector-Space

  mul-Vector-Space :
    type-Local-Commutative-Ring R → type-Vector-Space → type-Vector-Space
  mul-Vector-Space =
    mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  associative-add-Vector-Space :
    (v w x : type-Vector-Space) →
    add-Vector-Space (add-Vector-Space v w) x ＝
    add-Vector-Space v (add-Vector-Space w x)
  associative-add-Vector-Space = associative-add-Ab ab-Vector-Space

  left-unit-law-add-Vector-Space :
    (v : type-Vector-Space) → add-Vector-Space zero-Vector-Space v ＝ v
  left-unit-law-add-Vector-Space = left-unit-law-add-Ab ab-Vector-Space

  right-unit-law-add-Vector-Space :
    (v : type-Vector-Space) → add-Vector-Space v zero-Vector-Space ＝ v
  right-unit-law-add-Vector-Space = right-unit-law-add-Ab ab-Vector-Space

  left-inverse-law-add-Vector-Space :
    (v : type-Vector-Space) →
    add-Vector-Space (neg-Vector-Space v) v ＝ zero-Vector-Space
  left-inverse-law-add-Vector-Space = left-inverse-law-add-Ab ab-Vector-Space

  right-inverse-law-add-Vector-Space :
    (v : type-Vector-Space) →
    add-Vector-Space v (neg-Vector-Space v) ＝ zero-Vector-Space
  right-inverse-law-add-Vector-Space = right-inverse-law-add-Ab ab-Vector-Space

  commutative-add-Vector-Space :
    (v w : type-Vector-Space) → add-Vector-Space v w ＝ add-Vector-Space w v
  commutative-add-Vector-Space = commutative-add-Ab ab-Vector-Space

  left-unit-law-mul-Vector-Space :
    (v : type-Vector-Space) →
    mul-Vector-Space (one-Local-Commutative-Ring R) v ＝ v
  left-unit-law-mul-Vector-Space =
    left-unit-law-mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  left-distributive-mul-add-Vector-Space :
    (r : type-Local-Commutative-Ring R) (v w : type-Vector-Space) →
    mul-Vector-Space r (add-Vector-Space v w) ＝
    add-Vector-Space (mul-Vector-Space r v) (mul-Vector-Space r w)
  left-distributive-mul-add-Vector-Space =
    left-distributive-mul-add-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  right-distributive-mul-add-Vector-Space :
    (r s : type-Local-Commutative-Ring R) (v : type-Vector-Space) →
    mul-Vector-Space (add-Local-Commutative-Ring R r s) v ＝
    add-Vector-Space (mul-Vector-Space r v) (mul-Vector-Space s v)
  right-distributive-mul-add-Vector-Space =
    right-distributive-mul-add-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  associative-mul-Vector-Space :
    (r s : type-Local-Commutative-Ring R) (v : type-Vector-Space) →
    mul-Vector-Space (mul-Local-Commutative-Ring R r s) v ＝
    mul-Vector-Space r (mul-Vector-Space s v)
  associative-mul-Vector-Space =
    associative-mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  left-zero-law-mul-Vector-Space :
    (v : type-Vector-Space) →
    mul-Vector-Space (zero-Local-Commutative-Ring R) v ＝ zero-Vector-Space
  left-zero-law-mul-Vector-Space =
    left-zero-law-mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  right-zero-law-mul-Vector-Space :
    (r : type-Local-Commutative-Ring R) →
    mul-Vector-Space r zero-Vector-Space ＝ zero-Vector-Space
  right-zero-law-mul-Vector-Space =
    right-zero-law-mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  left-negative-law-mul-Vector-Space :
    (r : type-Local-Commutative-Ring R) (v : type-Vector-Space) →
    mul-Vector-Space (neg-Local-Commutative-Ring R r) v ＝
    neg-Vector-Space (mul-Vector-Space r v)
  left-negative-law-mul-Vector-Space =
    left-negative-law-mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  right-negative-law-mul-Vector-Space :
    (r : type-Local-Commutative-Ring R) (v : type-Vector-Space) →
    mul-Vector-Space r (neg-Vector-Space v) ＝
    neg-Vector-Space (mul-Vector-Space r v)
  right-negative-law-mul-Vector-Space =
    right-negative-law-mul-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)

  mul-neg-one-Vector-Space :
    (v : type-Vector-Space) →
    mul-Vector-Space
      ( neg-Local-Commutative-Ring R (one-Local-Commutative-Ring R))
      ( v) ＝
    neg-Vector-Space v
  mul-neg-one-Vector-Space =
    mul-neg-one-left-module-Commutative-Ring
      ( commutative-ring-Local-Commutative-Ring R)
      ( V)
```

### Any local commutative ring is a vector space over itself

```agda
vector-space-local-commutative-ring-Local-Commutative-Ring :
  {l : Level} (R : Local-Commutative-Ring l) → Vector-Space l R
vector-space-local-commutative-ring-Local-Commutative-Ring R =
  left-module-commutative-ring-Commutative-Ring
    ( commutative-ring-Local-Commutative-Ring R)
```
