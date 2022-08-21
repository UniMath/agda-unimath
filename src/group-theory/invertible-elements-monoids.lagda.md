---
title: Invertible elements in monoids
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module group-theory.invertible-elements-monoids where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using (is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.identity-types using (Id; inv; _∙_; ap)
open import foundation.propositions using
  ( all-elements-equal; is-prop-all-elements-equal; is-prop; prod-Prop; UU-Prop)
open import foundation.sets using (Id-Prop)
open import foundation.subtypes using (eq-type-subtype)
open import foundation.universe-levels using (Level; UU)

open import group-theory.monoids using
  ( Monoid; type-Monoid; mul-Monoid; unit-Monoid; set-Monoid;
    left-unit-law-mul-Monoid; associative-mul-Monoid; right-unit-law-mul-Monoid; mul-Monoid')
```

## Idea

An element `x ∈ M` in a monoid `M` is said to be invertible if there is an element `y ∈ M` such that `xy = e` and `yx = e`.

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
        Id (mul-Monoid M y x) (unit-Monoid M) ×
        Id (mul-Monoid M x y) (unit-Monoid M))
```

### Right inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-right-inverse-Monoid : type-Monoid M → UU l
  has-right-inverse-Monoid x =
    Σ ( type-Monoid M)
      ( λ y → Id (mul-Monoid M x y) (unit-Monoid M))
```

### Left inverses

```agda
module _
  {l : Level} (M : Monoid l)
  where

  has-left-inverse-Monoid : type-Monoid M → UU l
  has-left-inverse-Monoid x =
    Σ ( type-Monoid M)
      ( λ y → Id (mul-Monoid M y x) (unit-Monoid M))
```

## Properties

### Being invertible is a property

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
    is-prop-all-elements-equal (all-elements-equal-is-invertible-element-Monoid x)

  is-invertible-element-monoid-Prop : type-Monoid M → UU-Prop l
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
  pr1 (pr1 (is-contr-has-right-inverse-Monoid x (pair y (pair p q)))) = y
  pr2 (pr1 (is-contr-has-right-inverse-Monoid x (pair y (pair p q)))) = q
  pr2 (is-contr-has-right-inverse-Monoid x (pair y (pair p q))) (pair y' q') =
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
  pr1 (pr1 (is-contr-has-left-inverse-Monoid x (pair y (pair p q)))) = y
  pr2 (pr1 (is-contr-has-left-inverse-Monoid x (pair y (pair p q)))) = p
  pr2 (is-contr-has-left-inverse-Monoid x (pair y (pair p q))) (pair y' p') =
    eq-type-subtype
      ( λ u → Id-Prop (set-Monoid M) (mul-Monoid M u x) (unit-Monoid M))
      ( ( inv (left-unit-law-mul-Monoid M y)) ∙
        ( ( ap (mul-Monoid' M y) (inv p')) ∙
          ( ( associative-mul-Monoid M y' x y) ∙
            ( ( ap (mul-Monoid M y') q) ∙
              ( right-unit-law-mul-Monoid M y')))))
```
