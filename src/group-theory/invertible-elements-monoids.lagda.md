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

An element `x ∈ M` in a [monoid](group-theory.monoids.md) `M` is said to be
**invertible** if there is an element `y ∈ M` such that `xy = e` and `yx = e`.

## Definitions

### Invertible elements

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-invertible-element-Monoid : type-Monoid M → UU l
  is-invertible-element-Monoid x =
    Σ ( type-Monoid M)
      ( λ y →
        ( mul-Monoid M y x ＝ unit-Monoid M) ×
        ( mul-Monoid M x y ＝ unit-Monoid M))
```

### Right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-right-inverse-Monoid : type-Monoid M → UU l
  has-right-inverse-Monoid x =
    Σ ( type-Monoid M) (λ y → mul-Monoid M x y ＝ unit-Monoid M)
```

### Left inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-left-inverse-Monoid : type-Monoid M → UU l
  has-left-inverse-Monoid x =
    Σ ( type-Monoid M) (λ y → mul-Monoid M y x ＝ unit-Monoid M)
```

## Properties

### Inverses are left/right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-left-inverse-is-invertible-Monoid :
    (x : type-Monoid M) →
    is-invertible-element-Monoid M x → has-left-inverse-Monoid M x
  pr1 (has-left-inverse-is-invertible-Monoid x is-invertible-x) =
    pr1 is-invertible-x
  pr2 (has-left-inverse-is-invertible-Monoid x is-invertible-x) =
    pr1 (pr2 is-invertible-x)

  has-right-inverse-is-invertible-Monoid :
    (x : type-Monoid M) →
    is-invertible-element-Monoid M x → has-right-inverse-Monoid M x
  pr1 (has-right-inverse-is-invertible-Monoid x is-invertible-x) =
    pr1 is-invertible-x
  pr2 (has-right-inverse-is-invertible-Monoid x is-invertible-x) =
    pr2 (pr2 is-invertible-x)
```

### The inverse invertible element

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-right-inverse-left-inverse-Monoid :
    (x : type-Monoid M) (lx : has-left-inverse-Monoid M x) →
    has-right-inverse-Monoid M (pr1 lx)
  pr1 (has-right-inverse-left-inverse-Monoid x lx) = x
  pr2 (has-right-inverse-left-inverse-Monoid x lx) = pr2 lx

  has-left-inverse-right-inverse-Monoid :
    (x : type-Monoid M) (rx : has-right-inverse-Monoid M x) →
    has-left-inverse-Monoid M (pr1 rx)
  pr1 (has-left-inverse-right-inverse-Monoid x rx) = x
  pr2 (has-left-inverse-right-inverse-Monoid x rx) = pr2 rx

  is-invertible-element-inverse-Monoid :
    (x : type-Monoid M) (x' : is-invertible-element-Monoid M x) →
    is-invertible-element-Monoid M (pr1 x')
  pr1 (is-invertible-element-inverse-Monoid x x') = x
  pr1 (pr2 (is-invertible-element-inverse-Monoid x x')) = pr2 (pr2 x')
  pr2 (pr2 (is-invertible-element-inverse-Monoid x x')) = pr1 (pr2 x')
```

### Being invertible is a property

```agda
module _
  {l : Level} (M : Monoid l)
  where

  all-elements-equal-is-invertible-element-Monoid :
    (x : type-Monoid M) → all-elements-equal (is-invertible-element-Monoid M x)
  all-elements-equal-is-invertible-element-Monoid x (y , p , q) (y' , p' , q') =
    eq-type-subtype
      ( λ z →
        prod-Prop
          ( Id-Prop (set-Monoid M) (mul-Monoid M z x) (unit-Monoid M))
          ( Id-Prop (set-Monoid M) (mul-Monoid M x z) (unit-Monoid M)))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( ( inv (ap (λ z → mul-Monoid M z y) p')) ∙
          ( ( associative-mul-Monoid M y' x y) ∙
            ( ( ap (mul-Monoid M y') q) ∙
              ( right-unit-law-mul-Monoid M y')))))

  is-prop-is-invertible-element-Monoid :
    (x : type-Monoid M) → is-prop (is-invertible-element-Monoid M x)
  is-prop-is-invertible-element-Monoid x =
    is-prop-all-elements-equal
      ( all-elements-equal-is-invertible-element-Monoid x)

  is-invertible-element-monoid-Prop : type-Monoid M → Prop l
  pr1 (is-invertible-element-monoid-Prop x) = is-invertible-element-Monoid M x
  pr2 (is-invertible-element-monoid-Prop x) =
    is-prop-is-invertible-element-Monoid x
```

### Any invertible element of a monoid has a contractible type of right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-has-right-inverse-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (has-right-inverse-Monoid M x)
  pr1 (pr1 (is-contr-has-right-inverse-Monoid x (y , (p , q)))) = y
  pr2 (pr1 (is-contr-has-right-inverse-Monoid x (y , (p , q)))) = q
  pr2 (is-contr-has-right-inverse-Monoid x (y , (p , q))) (y' , q') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M x u) (unit-Monoid M))
      ( ( inv (right-unit-law-mul-Monoid M y)) ∙
        ( ( ap (mul-Monoid M y) (inv q')) ∙
          ( ( inv (associative-mul-Monoid M y x y')) ∙
            ( ( ap (mul-Monoid' M y') p) ∙
              ( left-unit-law-mul-Monoid M y')))))
```

### Any invertible element of a monoid has a contractible type of left inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  is-contr-has-left-inverse-Monoid :
    (x : type-Monoid M) → is-invertible-element-Monoid M x →
    is-contr (has-left-inverse-Monoid M x)
  pr1 (pr1 (is-contr-has-left-inverse-Monoid x (y , p , q))) = y
  pr2 (pr1 (is-contr-has-left-inverse-Monoid x (y , p , q))) = p
  pr2 (is-contr-has-left-inverse-Monoid x (y , p , q)) (y' , p') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M u x) (unit-Monoid M))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( ( ap (mul-Monoid' M y) (inv p')) ∙
          ( ( associative-mul-Monoid M y' x y) ∙
            ( ( ap (mul-Monoid M y') q) ∙
              ( right-unit-law-mul-Monoid M y')))))
```

### The unit of a Monoid is invertible

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-left-inverse-unit-Monoid : has-left-inverse-Monoid M (unit-Monoid M)
  pr1 has-left-inverse-unit-Monoid = unit-Monoid M
  pr2 has-left-inverse-unit-Monoid = left-unit-law-mul-Monoid M (unit-Monoid M)

  has-right-inverse-unit-Monoid : has-right-inverse-Monoid M (unit-Monoid M)
  pr1 has-right-inverse-unit-Monoid = unit-Monoid M
  pr2 has-right-inverse-unit-Monoid = left-unit-law-mul-Monoid M (unit-Monoid M)

  is-invertible-element-unit-Monoid :
    is-invertible-element-Monoid M (unit-Monoid M)
  pr1 is-invertible-element-unit-Monoid = unit-Monoid M
  pr1 (pr2 is-invertible-element-unit-Monoid) =
    left-unit-law-mul-Monoid M (unit-Monoid M)
  pr2 (pr2 is-invertible-element-unit-Monoid) =
    left-unit-law-mul-Monoid M (unit-Monoid M)
```

### Invertible elements are closed under multiplication

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-left-inverse-mul-Monoid :
    (x y : type-Monoid M) →
    has-left-inverse-Monoid M x →
    has-left-inverse-Monoid M y →
    has-left-inverse-Monoid M (mul-Monoid M x y)
  pr1 (has-left-inverse-mul-Monoid x y (lx , H) (ly , I)) = mul-Monoid M ly lx
  pr2 (has-left-inverse-mul-Monoid x y (lx , H) (ly , I)) =
    ( associative-mul-Monoid M ly lx (mul-Monoid M x y)) ∙
    ( ap
      ( mul-Monoid M ly)
      ( ( inv (associative-mul-Monoid M lx x y)) ∙
        ( ap (λ z → mul-Monoid M z y) H) ∙
        ( left-unit-law-mul-Monoid M y))) ∙
    ( I)

  has-right-inverse-mul-Monoid :
    (x y : type-Monoid M) →
    has-right-inverse-Monoid M x →
    has-right-inverse-Monoid M y →
    has-right-inverse-Monoid M (mul-Monoid M x y)
  pr1 (has-right-inverse-mul-Monoid x y (rx , H) (ry , I)) = mul-Monoid M ry rx
  pr2 (has-right-inverse-mul-Monoid x y (rx , H) (ry , I)) =
    ( associative-mul-Monoid M x y (mul-Monoid M ry rx)) ∙
    ( ap
      ( mul-Monoid M x)
      ( ( inv (associative-mul-Monoid M y ry rx)) ∙
        ( ap (λ z → mul-Monoid M z rx) I) ∙
        ( left-unit-law-mul-Monoid M rx))) ∙
    ( H)

  is-invertible-element-mul-Monoid :
    (x y : type-Monoid M) →
    is-invertible-element-Monoid M x →
    is-invertible-element-Monoid M y →
    is-invertible-element-Monoid M (mul-Monoid M x y)
  pr1 (is-invertible-element-mul-Monoid x y (x' , Lx , Rx) (y' , Ly , Ry)) =
    mul-Monoid M y' x'
  pr1
    ( pr2
      ( is-invertible-element-mul-Monoid x y (x' , Lx , Rx) (y' , Ly , Ry))) =
    pr2 (has-left-inverse-mul-Monoid x y (x' , Lx) (y' , Ly))
  pr2
    ( pr2
      ( is-invertible-element-mul-Monoid x y (x' , Lx , Rx) (y' , Ly , Ry))) =
    pr2 (has-right-inverse-mul-Monoid x y (x' , Rx) (y' , Ry))
```
