# Rational extension of the initial ring homomorphism in a ring extension of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.rational-extension-initial-hom-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.universe-levels

open import ring-theory.fractional-extension-initial-hom-ring-extensions-rational-numbers
open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
```

</details>

## Idea

Given a [ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md)
`R`, the
{{#concept "initial rational ring homomorphism" Agda=initial-hom-Rational-Extension-Ring}}
into `R`, is the unique [ring homomorphism](ring-theory.homomorphisms-rings.md)
from [`ℚ`](elementary-number-theory.ring-of-rational-numbers.md) to `R` ; it is
given by:

```text
(p/q : ℚ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)
```

where `ι : ℤ → R` is the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md) into
`R`.

## Definitions

### Rational extension of the initial ring homomorphism into a ring extension of `ℚ`

It is defined as `γ : (p/q : ℚ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)` where `ι : ℤ → R`
is the initial ring homomorphism.

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  map-initial-hom-Rational-Extension-Ring : ℚ → type-Rational-Extension-Ring R
  map-initial-hom-Rational-Extension-Ring =
    map-initial-hom-fraction-Rational-Extension-Ring R ∘ fraction-ℚ

  map-initial-hom-Rational-Extension-Ring' : ℚ → type-Rational-Extension-Ring R
  map-initial-hom-Rational-Extension-Ring' =
    map-initial-hom-fraction-Rational-Extension-Ring' R ∘ fraction-ℚ

  htpy-map-initial-hom-Rational-Extension-Ring' :
    map-initial-hom-Rational-Extension-Ring ~
    map-initial-hom-Rational-Extension-Ring'
  htpy-map-initial-hom-Rational-Extension-Ring' x =
    htpy-map-initial-hom-fraction-Rational-Extension-Ring' R (fraction-ℚ x)
```

## Properties

### Any ring homomorphism `ℚ → R` is homotopic to the rational initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  (f : rational-hom-Rational-Extension-Ring R)
  where

  htpy-map-initial-hom-Rational-Extension-Ring :
    ( map-rational-hom-Rational-Extension-Ring R f) ~
    ( map-initial-hom-Rational-Extension-Ring R)
  htpy-map-initial-hom-Rational-Extension-Ring x =
    ( ap
      ( map-rational-hom-Rational-Extension-Ring R f)
      ( inv (eq-mul-numerator-reciprocal-denominator-ℚ x))) ∙
    ( preserves-mul-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Extension-Ring R)
      ( f)) ∙
    ( ap-binary
      ( mul-Ring (ring-Rational-Extension-Ring R))
      ( htpy-map-integer-rational-hom-Rational-Extension-Ring
        ( R)
        ( f)
        ( numerator-ℚ x))
      ( htpy-map-reciprocal-rational-hom-Rational-Extension-Ring
        ( R)
        ( f)
        ( positive-denominator-ℚ x)))

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-rational-hom-Ring :
    ( map-hom-Ring ring-ℚ R f) ~
    ( map-initial-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f))
  htpy-map-rational-hom-Ring =
    htpy-map-initial-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### All ring homomorphisms `ℚ → R` into a ring extension of `ℚ` are equal

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  all-htpy-rational-hom-Rational-Extension-Ring :
    (f g : rational-hom-Rational-Extension-Ring R) →
    map-rational-hom-Rational-Extension-Ring R f ~
    map-rational-hom-Rational-Extension-Ring R g
  all-htpy-rational-hom-Rational-Extension-Ring f g x =
    ( htpy-map-initial-hom-Rational-Extension-Ring R f x) ∙
    ( inv (htpy-map-initial-hom-Rational-Extension-Ring R g x))

  all-eq-rational-hom-Rational-Extension-Ring :
    (f g : rational-hom-Rational-Extension-Ring R) →
    f ＝ g
  all-eq-rational-hom-Rational-Extension-Ring f g =
    eq-htpy-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Extension-Ring R)
      ( f)
      ( g)
      ( all-htpy-rational-hom-Rational-Extension-Ring f g)

  is-prop-has-rational-hom-Rational-Extension-Ring :
    is-prop (rational-hom-Rational-Extension-Ring R)
  is-prop-has-rational-hom-Rational-Extension-Ring =
    is-prop-all-elements-equal all-eq-rational-hom-Rational-Extension-Ring

  has-rational-hom-prop-Rational-Extension-Ring : Prop l
  has-rational-hom-prop-Rational-Extension-Ring =
    ( rational-hom-Rational-Extension-Ring R ,
      is-prop-has-rational-hom-Rational-Extension-Ring)
```

### All ring homomorphisms `ℚ → R` into a ring are equal

```agda
module _
  {l : Level} (R : Ring l)
  where

  all-htpy-rational-hom-Ring : (f g : hom-Ring ring-ℚ R) →
    map-hom-Ring ring-ℚ R f ~ map-hom-Ring ring-ℚ R g
  all-htpy-rational-hom-Ring f =
    all-htpy-rational-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)

  all-eq-rational-hom-Ring : (f g : hom-Ring ring-ℚ R) → f ＝ g
  all-eq-rational-hom-Ring f g =
    eq-htpy-hom-Ring ring-ℚ R f g (all-htpy-rational-hom-Ring f g)

  is-prop-has-rational-hom-Ring : is-prop (hom-Ring ring-ℚ R)
  is-prop-has-rational-hom-Ring =
    is-prop-all-elements-equal all-eq-rational-hom-Ring

  has-rational-hom-prop-Ring : Prop l
  has-rational-hom-prop-Ring =
    hom-Ring ring-ℚ R , is-prop-has-rational-hom-Ring
```

### The rational initial ring map extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  htpy-integer-map-initial-hom-Rational-Extension-Ring :
    map-initial-hom-Rational-Extension-Ring R ∘ rational-ℤ ~
    map-initial-hom-integer-Rational-Extension-Ring R
  htpy-integer-map-initial-hom-Rational-Extension-Ring k =
    ( ap
      ( mul-Rational-Extension-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Extension-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Extension-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Extension-Ring R)
      ( map-initial-hom-integer-Rational-Extension-Ring R k))
```

### The rational initial ring map preserves one

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  preserves-one-initial-hom-Rational-Extension-Ring :
    map-initial-hom-Rational-Extension-Ring R one-ℚ ＝
    one-Ring (ring-Rational-Extension-Ring R)
  preserves-one-initial-hom-Rational-Extension-Ring =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring R)
      ( is-invertible-positive-integer-Rational-Extension-Ring R one-ℤ⁺)
```

### The rational initial ring map is a ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  opaque
    unfolding add-ℚ
    unfolding mul-ℚ
    unfolding rational-fraction-ℤ

    preserves-add-initial-hom-Rational-Extension-Ring :
      {x y : ℚ} →
      map-initial-hom-Rational-Extension-Ring R (x +ℚ y) ＝
      add-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-Rational-Extension-Ring R x)
        ( map-initial-hom-Rational-Extension-Ring R y)
    preserves-add-initial-hom-Rational-Extension-Ring {x} {y} =
      equational-reasoning
        map-initial-hom-Rational-Extension-Ring R (x +ℚ y)
        ＝ map-initial-hom-fraction-Rational-Extension-Ring
          ( R)
          ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          by
            eq-map-sim-fraction-map-initial-Rational-Extension-Ring
              ( R)
              ( symmetric-sim-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
                ( reduce-fraction-ℤ
                  ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
                ( sim-reduced-fraction-ℤ
                  ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
        ＝ add-Ring
          ( ring-Rational-Extension-Ring R)
          ( map-initial-hom-Rational-Extension-Ring R x)
          ( map-initial-hom-Rational-Extension-Ring R y)
          by (preserves-add-map-initial-hom-fraction-Rational-Extension-Ring R)

    preserves-mul-initial-hom-Rational-Extension-Ring :
      {x y : ℚ} →
      map-initial-hom-Rational-Extension-Ring R (x *ℚ y) ＝
      mul-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-Rational-Extension-Ring R x)
        ( map-initial-hom-Rational-Extension-Ring R y)
    preserves-mul-initial-hom-Rational-Extension-Ring {x} {y} =
      equational-reasoning
        map-initial-hom-Rational-Extension-Ring R (x *ℚ y)
        ＝ map-initial-hom-fraction-Rational-Extension-Ring
          ( R)
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          by
            eq-map-sim-fraction-map-initial-Rational-Extension-Ring
              ( R)
              ( symmetric-sim-fraction-ℤ
                ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
                ( reduce-fraction-ℤ
                  ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
                ( sim-reduced-fraction-ℤ
                  ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
        ＝ mul-Ring
          ( ring-Rational-Extension-Ring R)
          ( map-initial-hom-Rational-Extension-Ring R x)
          ( map-initial-hom-Rational-Extension-Ring R y)
          by (preserves-mul-map-initial-hom-fraction-Rational-Extension-Ring R)

  initial-hom-Rational-Extension-Ring : rational-hom-Rational-Extension-Ring R
  pr1 initial-hom-Rational-Extension-Ring =
    ( map-initial-hom-Rational-Extension-Ring R ,
      preserves-add-initial-hom-Rational-Extension-Ring)
  pr2 initial-hom-Rational-Extension-Ring =
    ( preserves-mul-initial-hom-Rational-Extension-Ring ,
      preserves-one-initial-hom-Rational-Extension-Ring R)
```

### The type of ring homomorphisms from `ℚ` to a ring extension of `ℚ` is contractible

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  is-contr-rational-hom-Rational-Extension-Ring :
    is-contr (rational-hom-Rational-Extension-Ring R)
  is-contr-rational-hom-Rational-Extension-Ring =
    ( initial-hom-Rational-Extension-Ring R) ,
    ( λ g →
      eq-htpy-hom-Ring
        ( ring-ℚ)
        ( ring-Rational-Extension-Ring R)
        ( initial-hom-Rational-Extension-Ring R)
        ( g)
        ( inv ∘ htpy-map-initial-hom-Rational-Extension-Ring R g))

  is-prop-rational-hom-Rational-Extension-Ring :
    is-prop (rational-hom-Rational-Extension-Ring R)
  is-prop-rational-hom-Rational-Extension-Ring =
    is-prop-is-contr is-contr-rational-hom-Rational-Extension-Ring
```

### A ring `R` is a ring extension of `ℚ` if and only if there exists a ring homomorphism `ℚ → R`

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-rational-hom-is-rational-extension-Ring :
    is-rational-extension-Ring R → hom-Ring ring-ℚ R
  has-rational-hom-is-rational-extension-Ring =
    initial-hom-Rational-Extension-Ring ∘ pair R

  iff-is-rational-extension-has-rational-hom-Ring :
    hom-Ring ring-ℚ R ↔ is-rational-extension-Ring R
  iff-is-rational-extension-has-rational-hom-Ring =
    ( is-rational-extension-has-rational-hom-Ring R ,
      has-rational-hom-is-rational-extension-Ring)
```

### A ring `R` is a ring extension of `ℚ` if and only if the type of ring homomorphisms `ℚ → R` is contractible

```agda
module _
  {l : Level} (R : Ring l)
  where

  iff-is-rational-extension-is-contr-rational-hom-Ring :
    is-contr (hom-Ring ring-ℚ R) ↔ is-rational-extension-Ring R
  iff-is-rational-extension-is-contr-rational-hom-Ring =
    ( is-rational-extension-has-rational-hom-Ring R ∘ center) ,
    ( is-contr-rational-hom-Rational-Extension-Ring ∘ pair R)
```
