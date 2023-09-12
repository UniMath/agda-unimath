# Invertible elements in monoids

```agda
module group-theory.invertible-elements-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.monoids
```

</details>

## Idea

An element `x : M` in a [monoid](group-theory.monoids.md) `M` is said to be
**left invertible** if there is an element `y : M` such that `yx ＝ e`, and it
is said to be **right invertible** if there is an element `y : M` such that
`xy ＝ e`. The element `x` is said to be **invertible** if it has a **two-sided
inverse**, i.e., if if there is an element `y : M` such that `xy = e` and
`yx = e`. Left inverses of elements are also called **retractions** and right
inverses are also called **sections**.

## Definitions

### Right invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-right-inverse-element-Monoid : type-Monoid M → UU l
  is-right-inverse-element-Monoid y = mul-Monoid M x y ＝ unit-Monoid M

  is-right-invertible-element-Monoid : UU l
  is-right-invertible-element-Monoid =
    Σ (type-Monoid M) is-right-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  section-is-right-invertible-element-Monoid :
    is-right-invertible-element-Monoid M x → type-Monoid M
  section-is-right-invertible-element-Monoid = pr1

  is-right-inverse-section-is-right-invertible-element-Monoid :
    (H : is-right-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x
      ( section-is-right-invertible-element-Monoid H)
  is-right-inverse-section-is-right-invertible-element-Monoid = pr2
```

### Left invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-left-inverse-element-Monoid : type-Monoid M → UU l
  is-left-inverse-element-Monoid y = mul-Monoid M y x ＝ unit-Monoid M

  is-left-invertible-element-Monoid : UU l
  is-left-invertible-element-Monoid =
    Σ (type-Monoid M) is-left-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  retraction-is-left-invertible-element-Monoid :
    is-left-invertible-element-Monoid M x → type-Monoid M
  retraction-is-left-invertible-element-Monoid = pr1

  is-left-inverse-retraction-is-left-invertible-element-Monoid :
    (H : is-left-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x
      ( retraction-is-left-invertible-element-Monoid H)
  is-left-inverse-retraction-is-left-invertible-element-Monoid = pr2
```

### Invertible elements

```agda
module _
  {l : Level} (M : Monoid l) (x : type-Monoid M)
  where

  is-inverse-element-Monoid : type-Monoid M → UU l
  is-inverse-element-Monoid y =
    is-right-inverse-element-Monoid M x y ×
    is-left-inverse-element-Monoid M x y

  is-invertible-element-Monoid : UU l
  is-invertible-element-Monoid =
    Σ (type-Monoid M) is-inverse-element-Monoid

module _
  {l : Level} (M : Monoid l) {x : type-Monoid M}
  where

  inv-is-invertible-element-Monoid :
    is-invertible-element-Monoid M x → type-Monoid M
  inv-is-invertible-element-Monoid = pr1

  is-right-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-right-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-right-inverse-inv-is-invertible-element-Monoid H = pr1 (pr2 H)

  is-left-inverse-inv-is-invertible-element-Monoid :
    (H : is-invertible-element-Monoid M x) →
    is-left-inverse-element-Monoid M x (inv-is-invertible-element-Monoid H)
  is-left-inverse-inv-is-invertible-element-Monoid H = pr2 (pr2 H)
```

## Properties

### Being an invertible element is a property

```agda
module _
  {l : Level} (M : Monoid l)
  where

  all-elements-equal-is-invertible-element-Monoid :
    (x : type-Monoid M) → all-elements-equal (is-invertible-element-Monoid M x)
  all-elements-equal-is-invertible-element-Monoid x
    (pair y (pair p q)) (pair y' (pair p' q')) =
    eq-type-subtype
      ( λ z →
        prod-Prop
          ( Id-Prop (set-Monoid M) (mul-Monoid M x z) (unit-Monoid M))
          ( Id-Prop (set-Monoid M) (mul-Monoid M z x) (unit-Monoid M)))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( ( inv (ap (λ z → mul-Monoid M z y) q')) ∙
          ( ( associative-mul-Monoid M y' x y) ∙
            ( ( ap (mul-Monoid M y') p) ∙
              ( right-unit-law-mul-Monoid M y')))))

  is-prop-is-invertible-element-Monoid :
    (x : type-Monoid M) → is-prop (is-invertible-element-Monoid M x)
  is-prop-is-invertible-element-Monoid x =
    is-prop-all-elements-equal
      ( all-elements-equal-is-invertible-element-Monoid x)

  is-invertible-element-monoid-Prop : type-Monoid M → Prop l
  pr1 (is-invertible-element-monoid-Prop x) =
    is-invertible-element-Monoid M x
  pr2 (is-invertible-element-monoid-Prop x) =
    is-prop-is-invertible-element-Monoid x
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-is-right-invertible-element-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (is-right-invertible-element-Monoid M x)
  pr1 (pr1 (is-contr-is-right-invertible-element-Monoid x (y , p , q))) = y
  pr2 (pr1 (is-contr-is-right-invertible-element-Monoid x (y , p , q))) = p
  pr2 (is-contr-is-right-invertible-element-Monoid x (y , p , q)) (y' , q') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M x u) (unit-Monoid M))
      ( ( inv (right-unit-law-mul-Monoid M y)) ∙
        ( ap (mul-Monoid M y) (inv q')) ∙
        ( inv (associative-mul-Monoid M y x y')) ∙
        ( ap (mul-Monoid' M y') q) ∙
        ( left-unit-law-mul-Monoid M y'))
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-has-left-inverse-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (is-left-invertible-element-Monoid M x)
  pr1 (pr1 (is-contr-has-left-inverse-Monoid x (y , p , q))) = y
  pr2 (pr1 (is-contr-has-left-inverse-Monoid x (y , p , q))) = q
  pr2 (is-contr-has-left-inverse-Monoid x (y , p , q)) (y' , p') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M u x) (unit-Monoid M))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( ap (mul-Monoid' M y) (inv p')) ∙
        ( associative-mul-Monoid M y' x y) ∙
        ( ap (mul-Monoid M y') p) ∙
        ( right-unit-law-mul-Monoid M y'))
```

### The unit of a monoid is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-invertible-element-unit-Monoid :
    is-invertible-element-Monoid M (unit-Monoid M)
  pr1 is-invertible-element-unit-Monoid =
    unit-Monoid M
  pr1 (pr2 is-invertible-element-unit-Monoid) =
    left-unit-law-mul-Monoid M (unit-Monoid M)
  pr2 (pr2 is-invertible-element-unit-Monoid) =
    left-unit-law-mul-Monoid M (unit-Monoid M)
```

### The product of two invertible elements is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  private
    infix 45 _*_
    _*_ = mul-Monoid M

  is-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-invertible-element-Monoid M x → is-invertible-element-Monoid M y →
    is-invertible-element-Monoid M (mul-Monoid M x y)
  pr1 (is-invertible-element-mul-Monoid x y (u , p , q) (v , r , s)) =
    v * u
  pr1 (pr2 (is-invertible-element-mul-Monoid x y (u , p , q) (v , r , s))) =
    equational-reasoning
      (x * y) * (v * u)
      ＝ x * (y * (v * u))
        by associative-mul-Monoid M x y (v * u)
      ＝ x * ((y * v) * u)
        by ap (x *_) (inv (associative-mul-Monoid M y v u))
      ＝ x * (unit-Monoid M * u)
        by ap (x *_) (ap (_* u) r)
      ＝ x * u
        by ap (x *_) (left-unit-law-mul-Monoid M u)
      ＝ unit-Monoid M
        by p
  pr2 (pr2 (is-invertible-element-mul-Monoid x y (u , p , q) (v , r , s))) =
    equational-reasoning
      (v * u) * (x * y)
      ＝ v * (u * (x * y))
        by associative-mul-Monoid M v u (x * y)
      ＝ v * ((u * x) * y)
        by ap (v *_) (inv (associative-mul-Monoid M u x y))
      ＝ v * (unit-Monoid M * y)
        by ap (v *_) (ap (_* y) q)
      ＝ v * y
        by ap (v *_) (left-unit-law-mul-Monoid M y)
      ＝ unit-Monoid M
        by s
```

### The inverse of an invertible element is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-invertible-element-inv-is-invertible-element-Monoid :
    {x : type-Monoid M} (H : is-invertible-element-Monoid M x) →
    is-invertible-element-Monoid M (inv-is-invertible-element-Monoid M H)
  pr1 (is-invertible-element-inv-is-invertible-element-Monoid {x} H) = x
  pr1 (pr2 (is-invertible-element-inv-is-invertible-element-Monoid H)) =
    is-left-inverse-inv-is-invertible-element-Monoid M H
  pr2 (pr2 (is-invertible-element-inv-is-invertible-element-Monoid H)) =
    is-right-inverse-inv-is-invertible-element-Monoid M H
```
