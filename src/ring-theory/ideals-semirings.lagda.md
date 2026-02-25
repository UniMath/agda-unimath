# Ideals of semirings

```agda
module ring-theory.ideals-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import group-theory.submonoids

open import ring-theory.semirings
open import ring-theory.subsets-semirings
```

</details>

## Idea

An {{#concept "ideal" Disambiguation="in a semiring" Agda=ideal-Semiring}}
(resp. a
{{#concept "left" Disambiguation="ideal in a semiring" Agda=left-ideal-Semiring}}/{{#concept "right ideal" Disambiguation="in a semiring" Agda=right-ideal-Semiring}})
in a [semiring](ring-theory.semirings.md) `R` is an additive submodule of `R`
that is closed under multiplication by elements of `R` (from the left/right).

**Note.** This is the standard definition of ideals in semirings. However, such
two-sided ideals do not correspond uniquely to
[congruences](ring-theory.congruence-relations-semirings.md) on `R`. If we ask
in addition that the underlying additive submodule is normal, then we get unique
correspondence to congruences. We will call such ideals _normal_.

## Definitions

### Additive submonoids

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-additive-submonoid-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-additive-submonoid-Semiring =
    is-submonoid-subset-Monoid (additive-monoid-Semiring R)
```

### Left ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-left-ideal-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-left-ideal-subset-Semiring P =
    is-additive-submonoid-Semiring R P ×
    is-closed-under-left-multiplication-subset-Semiring R P

left-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
left-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-left-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : left-ideal-Semiring l2 R)
  where

  subset-left-ideal-Semiring : subset-Semiring l2 R
  subset-left-ideal-Semiring = pr1 I

  is-in-left-ideal-Semiring : type-Semiring R → UU l2
  is-in-left-ideal-Semiring x = type-Prop (subset-left-ideal-Semiring x)

  type-left-ideal-Semiring : UU (l1 ⊔ l2)
  type-left-ideal-Semiring = type-subset-Semiring R subset-left-ideal-Semiring

  inclusion-left-ideal-Semiring : type-left-ideal-Semiring → type-Semiring R
  inclusion-left-ideal-Semiring =
    inclusion-subset-Semiring R subset-left-ideal-Semiring

  ap-inclusion-left-ideal-Semiring :
    (x y : type-left-ideal-Semiring) → x ＝ y →
    inclusion-left-ideal-Semiring x ＝ inclusion-left-ideal-Semiring y
  ap-inclusion-left-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-left-ideal-Semiring

  is-in-subset-inclusion-left-ideal-Semiring :
    (x : type-left-ideal-Semiring) →
    is-in-left-ideal-Semiring (inclusion-left-ideal-Semiring x)
  is-in-subset-inclusion-left-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-left-ideal-Semiring

  is-closed-under-eq-left-ideal-Semiring :
    {x y : type-Semiring R} → is-in-left-ideal-Semiring x →
    (x ＝ y) → is-in-left-ideal-Semiring y
  is-closed-under-eq-left-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-left-ideal-Semiring

  is-closed-under-eq-left-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-left-ideal-Semiring y →
    (x ＝ y) → is-in-left-ideal-Semiring x
  is-closed-under-eq-left-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-left-ideal-Semiring

  is-left-ideal-subset-left-ideal-Semiring :
    is-left-ideal-subset-Semiring R subset-left-ideal-Semiring
  is-left-ideal-subset-left-ideal-Semiring = pr2 I

  is-additive-submonoid-left-ideal-Semiring :
    is-additive-submonoid-Semiring R subset-left-ideal-Semiring
  is-additive-submonoid-left-ideal-Semiring =
    pr1 is-left-ideal-subset-left-ideal-Semiring

  contains-zero-left-ideal-Semiring :
    is-in-left-ideal-Semiring (zero-Semiring R)
  contains-zero-left-ideal-Semiring =
    pr1 is-additive-submonoid-left-ideal-Semiring

  is-closed-under-addition-left-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-left-ideal-Semiring
  is-closed-under-addition-left-ideal-Semiring =
    pr2 is-additive-submonoid-left-ideal-Semiring

  is-closed-under-left-multiplication-left-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R
      subset-left-ideal-Semiring
  is-closed-under-left-multiplication-left-ideal-Semiring =
    pr2 is-left-ideal-subset-left-ideal-Semiring
```

### Right ideals

```agda
module _
  {l1 : Level} (R : Semiring l1)
  where

  is-right-ideal-subset-Semiring :
    {l2 : Level} → subset-Semiring l2 R → UU (l1 ⊔ l2)
  is-right-ideal-subset-Semiring P =
    is-additive-submonoid-Semiring R P ×
    is-closed-under-right-multiplication-subset-Semiring R P

right-ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
right-ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-right-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : right-ideal-Semiring l2 R)
  where

  subset-right-ideal-Semiring : subset-Semiring l2 R
  subset-right-ideal-Semiring = pr1 I

  is-in-right-ideal-Semiring : type-Semiring R → UU l2
  is-in-right-ideal-Semiring x = type-Prop (subset-right-ideal-Semiring x)

  type-right-ideal-Semiring : UU (l1 ⊔ l2)
  type-right-ideal-Semiring =
    type-subset-Semiring R subset-right-ideal-Semiring

  inclusion-right-ideal-Semiring : type-right-ideal-Semiring → type-Semiring R
  inclusion-right-ideal-Semiring =
    inclusion-subset-Semiring R subset-right-ideal-Semiring

  ap-inclusion-right-ideal-Semiring :
    (x y : type-right-ideal-Semiring) → x ＝ y →
    inclusion-right-ideal-Semiring x ＝ inclusion-right-ideal-Semiring y
  ap-inclusion-right-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-right-ideal-Semiring

  is-in-subset-inclusion-right-ideal-Semiring :
    (x : type-right-ideal-Semiring) →
    is-in-right-ideal-Semiring (inclusion-right-ideal-Semiring x)
  is-in-subset-inclusion-right-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-right-ideal-Semiring

  is-closed-under-eq-right-ideal-Semiring :
    {x y : type-Semiring R} → is-in-right-ideal-Semiring x →
    (x ＝ y) → is-in-right-ideal-Semiring y
  is-closed-under-eq-right-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-right-ideal-Semiring

  is-closed-under-eq-right-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-right-ideal-Semiring y →
    (x ＝ y) → is-in-right-ideal-Semiring x
  is-closed-under-eq-right-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-right-ideal-Semiring

  is-right-ideal-subset-right-ideal-Semiring :
    is-right-ideal-subset-Semiring R subset-right-ideal-Semiring
  is-right-ideal-subset-right-ideal-Semiring = pr2 I

  is-additive-submonoid-right-ideal-Semiring :
    is-additive-submonoid-Semiring R subset-right-ideal-Semiring
  is-additive-submonoid-right-ideal-Semiring =
    pr1 is-right-ideal-subset-right-ideal-Semiring

  contains-zero-right-ideal-Semiring :
    is-in-right-ideal-Semiring (zero-Semiring R)
  contains-zero-right-ideal-Semiring =
    pr1 is-additive-submonoid-right-ideal-Semiring

  is-closed-under-addition-right-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-right-ideal-Semiring
  is-closed-under-addition-right-ideal-Semiring =
    pr2 is-additive-submonoid-right-ideal-Semiring

  is-closed-under-right-multiplication-right-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R
      subset-right-ideal-Semiring
  is-closed-under-right-multiplication-right-ideal-Semiring =
    pr2 is-right-ideal-subset-right-ideal-Semiring
```

### Two-sided ideals

```agda
is-ideal-subset-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (P : subset-Semiring l2 R) → UU (l1 ⊔ l2)
is-ideal-subset-Semiring R P =
  is-additive-submonoid-Semiring R P ×
  ( is-closed-under-left-multiplication-subset-Semiring R P ×
    is-closed-under-right-multiplication-subset-Semiring R P)

ideal-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
ideal-Semiring l R =
  Σ (subset-Semiring l R) (is-ideal-subset-Semiring R)

module _
  {l1 l2 : Level} (R : Semiring l1) (I : ideal-Semiring l2 R)
  where

  subset-ideal-Semiring : subset-Semiring l2 R
  subset-ideal-Semiring = pr1 I

  is-in-ideal-Semiring : type-Semiring R → UU l2
  is-in-ideal-Semiring =
    is-in-subset-Semiring R subset-ideal-Semiring

  is-prop-is-in-ideal-Semiring :
    (x : type-Semiring R) → is-prop (is-in-ideal-Semiring x)
  is-prop-is-in-ideal-Semiring =
    is-prop-is-in-subset-Semiring R subset-ideal-Semiring

  type-ideal-Semiring : UU (l1 ⊔ l2)
  type-ideal-Semiring =
    type-subset-Semiring R subset-ideal-Semiring

  inclusion-ideal-Semiring :
    type-ideal-Semiring → type-Semiring R
  inclusion-ideal-Semiring =
    inclusion-subset-Semiring R subset-ideal-Semiring

  ap-inclusion-ideal-Semiring :
    (x y : type-ideal-Semiring) → x ＝ y →
    inclusion-ideal-Semiring x ＝ inclusion-ideal-Semiring y
  ap-inclusion-ideal-Semiring =
    ap-inclusion-subset-Semiring R subset-ideal-Semiring

  is-in-subset-inclusion-ideal-Semiring :
    (x : type-ideal-Semiring) →
    is-in-ideal-Semiring (inclusion-ideal-Semiring x)
  is-in-subset-inclusion-ideal-Semiring =
    is-in-subset-inclusion-subset-Semiring R subset-ideal-Semiring

  is-closed-under-eq-ideal-Semiring :
    {x y : type-Semiring R} → is-in-ideal-Semiring x →
    (x ＝ y) → is-in-ideal-Semiring y
  is-closed-under-eq-ideal-Semiring =
    is-closed-under-eq-subset-Semiring R subset-ideal-Semiring

  is-closed-under-eq-ideal-Semiring' :
    {x y : type-Semiring R} → is-in-ideal-Semiring y →
    (x ＝ y) → is-in-ideal-Semiring x
  is-closed-under-eq-ideal-Semiring' =
    is-closed-under-eq-subset-Semiring' R subset-ideal-Semiring

  is-ideal-subset-ideal-Semiring :
    is-ideal-subset-Semiring R subset-ideal-Semiring
  is-ideal-subset-ideal-Semiring = pr2 I

  is-additive-submonoid-ideal-Semiring :
    is-additive-submonoid-Semiring R subset-ideal-Semiring
  is-additive-submonoid-ideal-Semiring =
    pr1 is-ideal-subset-ideal-Semiring

  contains-zero-ideal-Semiring :
    is-in-ideal-Semiring (zero-Semiring R)
  contains-zero-ideal-Semiring =
    pr1 is-additive-submonoid-ideal-Semiring

  is-closed-under-addition-ideal-Semiring :
    is-closed-under-addition-subset-Semiring R subset-ideal-Semiring
  is-closed-under-addition-ideal-Semiring =
    pr2 is-additive-submonoid-ideal-Semiring

  is-closed-under-left-multiplication-ideal-Semiring :
    is-closed-under-left-multiplication-subset-Semiring R subset-ideal-Semiring
  is-closed-under-left-multiplication-ideal-Semiring =
    pr1 (pr2 is-ideal-subset-ideal-Semiring)

  is-closed-under-right-multiplication-ideal-Semiring :
    is-closed-under-right-multiplication-subset-Semiring R subset-ideal-Semiring
  is-closed-under-right-multiplication-ideal-Semiring =
    pr2 (pr2 is-ideal-subset-ideal-Semiring)

  submonoid-ideal-Semiring : Submonoid l2 (additive-monoid-Semiring R)
  pr1 submonoid-ideal-Semiring = subset-ideal-Semiring
  pr1 (pr2 submonoid-ideal-Semiring) = contains-zero-ideal-Semiring
  pr2 (pr2 submonoid-ideal-Semiring) = is-closed-under-addition-ideal-Semiring
```
