# Homomorphisms of ring extensions of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.homomorphisms-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.ring-extensions-rational-numbers
```

</details>

## Idea

{{#concept "Homomorphisms" Disambiguation="of ring extensions of ℚ" Agda=hom-Rational-Extension-Ring}}
of [rational extensions of ℚ](ring-theory.ring-extensions-rational-numbers.md)
are [homomorphisms](ring-theory.homomorphisms-rings.md) between their underlying
[rings](ring-theory.rings.md).

## Definitions

### Homorphisms of ring extensions of ℚ

```agda
module _
  {l1 l2 : Level}
  (A : Rational-Extension-Ring l1)
  (B : Rational-Extension-Ring l2)
  where

  hom-Rational-Extension-Ring : UU (l1 ⊔ l2)
  hom-Rational-Extension-Ring =
    hom-Ring
      ( ring-Rational-Extension-Ring A)
      ( ring-Rational-Extension-Ring B)

  map-hom-Rational-Extension-Ring :
    hom-Rational-Extension-Ring →
    type-Rational-Extension-Ring A →
    type-Rational-Extension-Ring B
  map-hom-Rational-Extension-Ring =
    map-hom-Ring
      ( ring-Rational-Extension-Ring A)
      ( ring-Rational-Extension-Ring B)
```
