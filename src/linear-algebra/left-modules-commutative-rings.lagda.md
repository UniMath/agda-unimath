# Left modules over commutative rings

```agda
module linear-algebra.left-modules-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.homomorphisms-commutative-rings

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.left-modules-rings
```

</details>

## Idea

A
{{#concept "left module" WD="left module" WDID="Q120721996" disambiguation="over a commutative ring" Agda=left-module-Commutative-Ring}}
over a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[left module](linear-algebra.left-modules-rings.md) over `R` viewed as a
[ring](ring-theory.rings.md).

## Definition

```agda
left-module-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
left-module-Commutative-Ring l2 R =
  left-module-Ring l2 (ring-Commutative-Ring R)
```

## Properties

```agda
module _
  {l1 l2 : Level} (R : Commutative-Ring l1)
  (M : left-module-Commutative-Ring l2 R)
  where

  ab-left-module-Commutative-Ring : Ab l2
  ab-left-module-Commutative-Ring =
    ab-left-module-Ring (ring-Commutative-Ring R) M

  set-left-module-Commutative-Ring : Set l2
  set-left-module-Commutative-Ring =
    set-left-module-Ring (ring-Commutative-Ring R) M

  type-left-module-Commutative-Ring : UU l2
  type-left-module-Commutative-Ring =
    type-left-module-Ring (ring-Commutative-Ring R) M

  add-left-module-Commutative-Ring :
    (x y : type-left-module-Commutative-Ring) →
    type-left-module-Commutative-Ring
  add-left-module-Commutative-Ring =
    add-left-module-Ring (ring-Commutative-Ring R) M

  mul-left-module-Commutative-Ring :
    type-Commutative-Ring R → type-left-module-Commutative-Ring →
    type-left-module-Commutative-Ring
  mul-left-module-Commutative-Ring =
    mul-left-module-Ring (ring-Commutative-Ring R) M

  zero-left-module-Commutative-Ring : type-left-module-Commutative-Ring
  zero-left-module-Commutative-Ring =
    zero-left-module-Ring (ring-Commutative-Ring R) M

  is-zero-prop-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring → Prop l2
  is-zero-prop-left-module-Commutative-Ring =
    is-zero-prop-left-module-Ring (ring-Commutative-Ring R) M

  is-zero-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring → UU l2
  is-zero-left-module-Commutative-Ring =
    is-zero-left-module-Ring (ring-Commutative-Ring R) M

  neg-left-module-Commutative-Ring :
    type-left-module-Commutative-Ring → type-left-module-Commutative-Ring
  neg-left-module-Commutative-Ring =
    neg-left-module-Ring (ring-Commutative-Ring R) M

  associative-add-left-module-Commutative-Ring :
    (x y z : type-left-module-Commutative-Ring) →
    add-left-module-Commutative-Ring (add-left-module-Commutative-Ring x y) z ＝
    add-left-module-Commutative-Ring x (add-left-module-Commutative-Ring y z)
  associative-add-left-module-Commutative-Ring =
    associative-add-left-module-Ring (ring-Commutative-Ring R) M

  commutative-add-left-module-Commutative-Ring :
    (x y : type-left-module-Commutative-Ring) →
    add-left-module-Commutative-Ring x y ＝
    add-left-module-Commutative-Ring y x
  commutative-add-left-module-Commutative-Ring =
    commutative-add-left-module-Ring (ring-Commutative-Ring R) M

  left-unit-law-add-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    add-left-module-Commutative-Ring zero-left-module-Commutative-Ring x ＝ x
  left-unit-law-add-left-module-Commutative-Ring =
    left-unit-law-add-left-module-Ring (ring-Commutative-Ring R) M

  right-unit-law-add-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    add-left-module-Commutative-Ring x zero-left-module-Commutative-Ring ＝ x
  right-unit-law-add-left-module-Commutative-Ring =
    right-unit-law-add-left-module-Ring (ring-Commutative-Ring R) M

  left-inverse-law-add-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    add-left-module-Commutative-Ring (neg-left-module-Commutative-Ring x) x ＝
    zero-left-module-Commutative-Ring
  left-inverse-law-add-left-module-Commutative-Ring =
    left-inverse-law-add-left-module-Ring (ring-Commutative-Ring R) M

  right-inverse-law-add-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    add-left-module-Commutative-Ring x (neg-left-module-Commutative-Ring x) ＝
    zero-left-module-Commutative-Ring
  right-inverse-law-add-left-module-Commutative-Ring =
    right-inverse-law-add-left-module-Ring (ring-Commutative-Ring R) M

  left-unit-law-mul-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring (one-Commutative-Ring R) x ＝ x
  left-unit-law-mul-left-module-Commutative-Ring =
    left-unit-law-mul-left-module-Ring (ring-Commutative-Ring R) M

  left-distributive-mul-add-left-module-Commutative-Ring :
    (r : type-Commutative-Ring R) (x y : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring r (add-left-module-Commutative-Ring x y) ＝
    add-left-module-Commutative-Ring
      ( mul-left-module-Commutative-Ring r x)
      ( mul-left-module-Commutative-Ring r y)
  left-distributive-mul-add-left-module-Commutative-Ring =
    left-distributive-mul-add-left-module-Ring (ring-Commutative-Ring R) M

  right-distributive-mul-add-left-module-Commutative-Ring :
    (r s : type-Commutative-Ring R) (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring (add-Commutative-Ring R r s) x ＝
    add-left-module-Commutative-Ring
      ( mul-left-module-Commutative-Ring r x)
      ( mul-left-module-Commutative-Ring s x)
  right-distributive-mul-add-left-module-Commutative-Ring =
    right-distributive-mul-add-left-module-Ring (ring-Commutative-Ring R) M

  associative-mul-left-module-Commutative-Ring :
    (r s : type-Commutative-Ring R) (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring (mul-Commutative-Ring R r s) x ＝
    mul-left-module-Commutative-Ring r (mul-left-module-Commutative-Ring s x)
  associative-mul-left-module-Commutative-Ring =
    associative-mul-left-module-Ring (ring-Commutative-Ring R) M

  left-zero-law-mul-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring (zero-Commutative-Ring R) x ＝
    zero-left-module-Commutative-Ring
  left-zero-law-mul-left-module-Commutative-Ring =
    left-zero-law-mul-left-module-Ring (ring-Commutative-Ring R) M

  right-zero-law-mul-left-module-Commutative-Ring :
    (r : type-Commutative-Ring R) →
    mul-left-module-Commutative-Ring r zero-left-module-Commutative-Ring ＝
    zero-left-module-Commutative-Ring
  right-zero-law-mul-left-module-Commutative-Ring =
    right-zero-law-mul-left-module-Ring (ring-Commutative-Ring R) M

  left-negative-law-mul-left-module-Commutative-Ring :
    (r : type-Commutative-Ring R) (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring (neg-Commutative-Ring R r) x ＝
    neg-left-module-Commutative-Ring (mul-left-module-Commutative-Ring r x)
  left-negative-law-mul-left-module-Commutative-Ring =
    left-negative-law-mul-left-module-Ring (ring-Commutative-Ring R) M

  right-negative-law-mul-left-module-Commutative-Ring :
    (r : type-Commutative-Ring R) (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring r (neg-left-module-Commutative-Ring x) ＝
    neg-left-module-Commutative-Ring (mul-left-module-Commutative-Ring r x)
  right-negative-law-mul-left-module-Commutative-Ring =
    right-negative-law-mul-left-module-Ring (ring-Commutative-Ring R) M

  mul-neg-one-left-module-Commutative-Ring :
    (x : type-left-module-Commutative-Ring) →
    mul-left-module-Commutative-Ring
      ( neg-Commutative-Ring R (one-Commutative-Ring R))
      ( x) ＝
    neg-left-module-Commutative-Ring x
  mul-neg-one-left-module-Commutative-Ring =
    mul-neg-one-left-module-Ring (ring-Commutative-Ring R) M
```

## Properties

### Any commutative ring is a left module over itself

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  left-module-commutative-ring-Commutative-Ring :
    left-module-Commutative-Ring l R
  left-module-commutative-ring-Commutative-Ring =
    left-module-ring-Ring (ring-Commutative-Ring R)
```

### Constructing a left module over a commutative ring from axioms

```agda
make-left-module-Commutative-Ring :
  {l1 l2 : Level} →
  (R : Commutative-Ring l1) (A : Ab l2) →
  (mul-left : type-Commutative-Ring R → type-Ab A → type-Ab A) →
  (left-distributive-mul-add :
    (r : type-Commutative-Ring R) (a b : type-Ab A) →
    mul-left r (add-Ab A a b) ＝ add-Ab A (mul-left r a) (mul-left r b)) →
  (right-distributive-mul-add :
    (r s : type-Commutative-Ring R) (a : type-Ab A) →
    mul-left (add-Commutative-Ring R r s) a ＝
    add-Ab A (mul-left r a) (mul-left s a)) →
  (left-unit-law-mul :
    (a : type-Ab A) → mul-left (one-Commutative-Ring R) a ＝ a) →
  (associative-mul :
    (r s : type-Commutative-Ring R) (a : type-Ab A) →
    mul-left (mul-Commutative-Ring R r s) a ＝ mul-left r (mul-left s a)) →
  left-module-Commutative-Ring l2 R
make-left-module-Commutative-Ring R =
  make-left-module-Ring (ring-Commutative-Ring R)
```

### Given a left module over `S`, a commutative ring homomorphism `R → S` induces a left module over `R`

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (S : Commutative-Ring l2)
  (h : hom-Commutative-Ring R S)
  (M : left-module-Commutative-Ring l3 S)
  where

  left-module-hom-left-module-Commutative-Ring :
    left-module-Commutative-Ring l3 R
  left-module-hom-left-module-Commutative-Ring =
    left-module-hom-left-module-Ring
      ( ring-Commutative-Ring R)
      ( ring-Commutative-Ring S)
      ( h)
      ( M)
```

### A commutative ring homomorphism `R → S` induces the structure of an `R`-left module on `S`

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (S : Commutative-Ring l2)
  (h : hom-Commutative-Ring R S)
  where

  left-module-hom-Commutative-Ring : left-module-Commutative-Ring l2 R
  left-module-hom-Commutative-Ring =
    left-module-hom-Ring
      ( ring-Commutative-Ring R)
      ( ring-Commutative-Ring S)
      ( h)
```
