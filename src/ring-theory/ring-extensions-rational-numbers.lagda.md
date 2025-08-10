# Ring extensions of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.localizations-rings
open import ring-theory.rings
```

</details>

## Idea

For a [ring](ring-theory.rings.md) `R`, the following conditions are equivalent
propositions:

- the images of
  [positive integers](elementary-number-theory.positive-integers.md) by the
  [initial ring homomorphism](elementary-number-theory.ring-of-integers.md)) are
  [invertible elements](ring-theory.invertible-elements-rings.md), i.e., the
  initial ring homomorphism [inverts](ring-theory.localizations-rings.md) the
  subset of positive integers;
- there exist a [ring homomorphism](ring-theory.homomorphisms-rings.md) `ℚ → R`
  from the
  [ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
  to `R`;
- the type of ring homomorphisms `ℚ → R` is
  [contractible](foundation-core.contractible-types.md).

In that case, `R` is called a a
{{#concept "ring extension of ℚ" Agda=Rational-Extension-Ring}}.

The unique ring homomorphism from `ℚ` to a ring extension of `ℚ` is given by
`(p/q : ℚ) ↦ (ι p)(ι q)⁻¹` where `ι : ℤ → R` is the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md) in
`R`. It is defined in
[rational-extension-initial-hom-ring-extensions-rational-numbers](ring-theory.rational-extension-initial-hom-ring-extensions-rational-numbers.md).

## Definitions

### The predicate on a ring of being a ring extension of the rational numbers

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-extension-prop-Ring : Prop l
  is-rational-extension-prop-Ring =
    inverts-subset-prop-hom-Ring
      ( ℤ-Ring)
      ( R)
      ( subtype-positive-ℤ)
      ( initial-hom-Ring R)

  is-rational-extension-Ring : UU l
  is-rational-extension-Ring = type-Prop is-rational-extension-prop-Ring

  is-prop-is-rational-extension-Ring : is-prop is-rational-extension-Ring
  is-prop-is-rational-extension-Ring =
    is-prop-type-Prop is-rational-extension-prop-Ring
```

### The type of ring extensions of `ℚ`

```agda
Rational-Extension-Ring : (l : Level) → UU (lsuc l)
Rational-Extension-Ring l = Σ (Ring l) is-rational-extension-Ring

module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  ring-Rational-Extension-Ring : Ring l
  ring-Rational-Extension-Ring = pr1 R

  type-Rational-Extension-Ring : UU l
  type-Rational-Extension-Ring = type-Ring ring-Rational-Extension-Ring

  is-rational-extension-ring-Rational-Extension-Ring :
    is-rational-extension-Ring ring-Rational-Extension-Ring
  is-rational-extension-ring-Rational-Extension-Ring = pr2 R

  mul-Rational-Extension-Ring :
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring
  mul-Rational-Extension-Ring = mul-Ring ring-Rational-Extension-Ring

  add-Rational-Extension-Ring :
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring
  add-Rational-Extension-Ring = add-Ring ring-Rational-Extension-Ring

  is-invertible-positive-integer-Rational-Extension-Ring :
    (k : ℤ⁺) →
    is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( map-initial-hom-Ring ring-Rational-Extension-Ring (int-positive-ℤ k))
  is-invertible-positive-integer-Rational-Extension-Ring (k , k>0) =
    is-rational-extension-ring-Rational-Extension-Ring k k>0

  inv-positive-integer-Rational-Extension-Ring :
    ℤ⁺ → type-Rational-Extension-Ring
  inv-positive-integer-Rational-Extension-Ring k =
    inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( is-invertible-positive-integer-Rational-Extension-Ring k)

  left-inverse-law-positive-integer-Rational-Extension-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Extension-Ring)
      ( inv-positive-integer-Rational-Extension-Ring k)
      ( map-initial-hom-Ring ring-Rational-Extension-Ring (int-positive-ℤ k)) ＝
    one-Ring ring-Rational-Extension-Ring
  left-inverse-law-positive-integer-Rational-Extension-Ring (k , k>0) =
    is-left-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( is-rational-extension-ring-Rational-Extension-Ring k k>0)

  right-inverse-law-positive-integer-Rational-Extension-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Extension-Ring)
      ( map-initial-hom-Ring ring-Rational-Extension-Ring (int-positive-ℤ k))
      ( inv-positive-integer-Rational-Extension-Ring k) ＝
    one-Ring ring-Rational-Extension-Ring
  right-inverse-law-positive-integer-Rational-Extension-Ring (k , k>0) =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( is-rational-extension-ring-Rational-Extension-Ring k k>0)
```

### The initial ring homomorphism into a ring extension of `ℚ`

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  initial-hom-integer-Rational-Extension-Ring :
    hom-Ring ℤ-Ring (ring-Rational-Extension-Ring R)
  initial-hom-integer-Rational-Extension-Ring =
    initial-hom-Ring (ring-Rational-Extension-Ring R)

  map-initial-hom-integer-Rational-Extension-Ring :
    ℤ → type-Rational-Extension-Ring R
  map-initial-hom-integer-Rational-Extension-Ring =
    map-initial-hom-Ring (ring-Rational-Extension-Ring R)
```

### The type of rational homomorphisms into a ring extension of `ℚ`

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  rational-hom-Rational-Extension-Ring : UU l
  rational-hom-Rational-Extension-Ring =
    hom-Ring ring-ℚ (ring-Rational-Extension-Ring R)

  map-rational-hom-Rational-Extension-Ring :
    rational-hom-Rational-Extension-Ring → ℚ → type-Rational-Extension-Ring R
  map-rational-hom-Rational-Extension-Ring =
    map-hom-Ring ring-ℚ (ring-Rational-Extension-Ring R)
```

## Properties

### The inverse of the image of one in a ring extension of `ℚ` is one

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  eq-one-inv-positive-one-Rational-Extension-Ring :
    one-Ring (ring-Rational-Extension-Ring R) ＝
    inv-positive-integer-Rational-Extension-Ring R one-ℤ⁺
  eq-one-inv-positive-one-Rational-Extension-Ring =
    contraction-right-inverse-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring R)
      ( one-Ring (ring-Rational-Extension-Ring R))
      ( is-invertible-element-one-Ring (ring-Rational-Extension-Ring R))
      ( inv-positive-integer-Rational-Extension-Ring R one-ℤ⁺)
      ( ( ap
          ( mul-Ring'
            ( ring-Rational-Extension-Ring R)
            ( inv-positive-integer-Rational-Extension-Ring R one-ℤ⁺))
          ( inv
            ( preserves-one-initial-hom-Ring
              ( ring-Rational-Extension-Ring R)))) ∙
        ( right-inverse-law-positive-integer-Rational-Extension-Ring R one-ℤ⁺))
```

### A ring `R` that admits a ring homomorphism `ℚ → R` is a ring extension of `ℚ`

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-extension-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → is-rational-extension-Ring R
  is-rational-extension-has-rational-hom-Ring f =
    inv-tr
      ( inverts-subset-hom-Ring
        ( ℤ-Ring)
        ( R)
        ( subtype-positive-ℤ))
      ( contraction-initial-hom-Ring
        ( R)
        ( comp-hom-Ring ℤ-Ring ring-ℚ R f hom-ring-rational-ℤ))
      ( inverts-positive-integers-rational-hom-Ring R f)

  rational-ring-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → Rational-Extension-Ring l
  rational-ring-has-rational-hom-Ring f =
    ( R , is-rational-extension-has-rational-hom-Ring f)

  inv-positive-integer-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → (k : ℤ⁺) → type-Ring R
  inv-positive-integer-has-rational-hom-Ring =
    inv-positive-integer-Rational-Extension-Ring ∘
    rational-ring-has-rational-hom-Ring
```

### Any ring homomorphism `ℚ → R` is an extension of the initial ring homomorphism `ℤ → R`

```agda
module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-integer-rational-hom-Ring :
    ( map-hom-Ring ring-ℚ R f ∘ rational-ℤ) ~
    ( map-initial-hom-Ring R)
  htpy-map-integer-rational-hom-Ring k =
    inv
      ( htpy-initial-hom-Ring
        ( R)
        ( comp-hom-Ring
          ( ℤ-Ring)
          ( ring-ℚ)
          ( R)
          ( f)
          ( hom-ring-rational-ℤ))
        ( k))

module _
  {l : Level} (R : Rational-Extension-Ring l)
  (f : rational-hom-Rational-Extension-Ring R)
  where

  htpy-map-integer-rational-hom-Rational-Extension-Ring :
    ( map-rational-hom-Rational-Extension-Ring R f ∘ rational-ℤ) ~
    ( map-initial-hom-integer-Rational-Extension-Ring R)
  htpy-map-integer-rational-hom-Rational-Extension-Ring =
    htpy-map-integer-rational-hom-Ring (ring-Rational-Extension-Ring R) f
```

### Any ring homomorphism `ℚ → R` preserves reciprocals of positive integers

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  (f : rational-hom-Rational-Extension-Ring R)
  where

  htpy-map-reciprocal-rational-hom-Rational-Extension-Ring :
    map-rational-hom-Rational-Extension-Ring R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-Rational-Extension-Ring R
  htpy-map-reciprocal-rational-hom-Rational-Extension-Ring k =
    inv
      ( contraction-right-inverse-is-invertible-element-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ k))
        ( is-invertible-positive-integer-Rational-Extension-Ring R k)
        ( map-rational-hom-Rational-Extension-Ring
          ( R)
          ( f)
          ( reciprocal-rational-ℤ⁺ k))
        ( is-right-inverse-map-reciprocal))
    where

    is-right-inverse-map-reciprocal :
      is-right-inverse-element-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ k))
        ( map-rational-hom-Rational-Extension-Ring
          ( R)
          ( f)
          ( reciprocal-rational-ℤ⁺ k))
    is-right-inverse-map-reciprocal =
      ( ap
        ( mul-Ring'
          ( ring-Rational-Extension-Ring R)
          ( map-hom-Ring
            ( ring-ℚ)
            ( ring-Rational-Extension-Ring R)
            ( f)
            ( reciprocal-rational-ℤ⁺ k)))
        ( inv
          ( htpy-map-integer-rational-hom-Rational-Extension-Ring
            ( R)
            ( f)
            ( int-positive-ℤ k)))) ∙
      ( inv
        ( preserves-mul-hom-Ring
          ( ring-ℚ)
          ( ring-Rational-Extension-Ring R)
          ( f))) ∙
      ( ap
        ( map-hom-Ring ring-ℚ (ring-Rational-Extension-Ring R) f)
        ( right-inverse-law-reciprocal-rational-ℤ⁺
          k)) ∙
      ( preserves-one-hom-Ring ring-ℚ (ring-Rational-Extension-Ring R) f)

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-reciprocal-rational-hom-Ring :
    map-hom-Ring ring-ℚ R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-has-rational-hom-Ring R f
  htpy-map-reciprocal-rational-hom-Ring =
    htpy-map-reciprocal-rational-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

## See also

- [`rational-extension-initial-hom-ring-extensions-rational-numbers`](ring-theory.rational-extension-initial-hom-ring-extensions-rational-numbers.md):
  the initial ring homomorphism from `ℚ` into a rational extension of `ℚ`.
