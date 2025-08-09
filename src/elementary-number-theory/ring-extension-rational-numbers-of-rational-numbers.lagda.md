# The ring extension of rational numbers of the ring of rational numbers

```agda
module elementary-number-theory.ring-extension-rational-numbers-of-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-integers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.localizations-rings
open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
```

</details>

## Idea

The
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
is a [ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md) so
`ℚ` is the initial ring extension of `ℚ`: the type of
[ring homomorphisms](ring-theory.homomorphisms-rings.md) from `ℚ` to a ring
extension of `ℚ` is [contractible](foundation-core.contractible-types.md).

As a corollary, `ℚ` is the [localization](ring-theory.localizations-rings.md) of
`ℤ` at `ℤ⁺`: any ring homomorphism `ℤ → R` that inverts the positive integers
extends to a ring homomorphism `ℚ → R`.

## Definition

### `ℚ` is a rational extension of itself

```agda
is-rational-extension-ring-ℚ : is-rational-extension-Ring ring-ℚ
is-rational-extension-ring-ℚ =
  is-rational-extension-has-rational-hom-Ring
    ( ring-ℚ)
    ( id-hom-Ring ring-ℚ)

rational-extension-ring-ℚ : Rational-Extension-Ring lzero
rational-extension-ring-ℚ =
  ( ring-ℚ , is-rational-extension-ring-ℚ)
```

## Properties

### The ring of rational numbers is the initial ring extension of `ℚ`

```agda
module _
  {l : Level}
  where

  is-initial-rational-extension-ring-ℚ :
    (R : Rational-Extension-Ring l) →
    is-contr (hom-Rational-Extension-Ring rational-extension-ring-ℚ R)
  is-initial-rational-extension-ring-ℚ R =
    is-contr-rational-hom-Rational-Extension-Ring R
```

### The ring of rational numbers is the localization of the ring of integers at `ℤ⁺`

```agda
module _
  {l : Level}
  where

  universal-property-localization-positive-integers-ring-ℚ :
    universal-property-localization-subset-Ring
      ( l)
      ( ℤ-Ring)
      ( ring-ℚ)
      ( subtype-positive-ℤ)
      ( initial-hom-Ring ring-ℚ)
      ( is-rational-extension-ring-ℚ)
  universal-property-localization-positive-integers-ring-ℚ T =
    is-equiv-has-converse-is-prop
      ( is-prop-has-rational-hom-Ring T)
      ( is-prop-type-subtype
        ( inverts-subset-prop-hom-Ring ℤ-Ring T subtype-positive-ℤ)
        ( is-prop-is-contr (is-initial-ℤ-Ring T)))
      ( λ (f , H) →
        initial-hom-Rational-Extension-Ring
          ( ( T) ,
            ( inv-tr
              ( inverts-subset-hom-Ring ℤ-Ring T subtype-positive-ℤ)
              ( contraction-initial-hom-Ring T f)
              ( H))))
```
