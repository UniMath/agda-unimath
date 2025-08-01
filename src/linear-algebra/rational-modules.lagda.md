# Rational modules

```agda
{-# OPTIONS --lossy-unification #-}

module linear-algebra.rational-modules where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-integers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.endomorphism-rings-abelian-groups
open import group-theory.homomorphisms-abelian-groups
open import group-theory.integer-multiples-of-elements-abelian-groups
open import group-theory.isomorphisms-abelian-groups

open import linear-algebra.left-modules-rings
open import linear-algebra.right-modules-rings

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.opposite-rings
open import ring-theory.rational-extensions-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "rational module" Agda=Rational-Module}} is an
[abelian group](group-theory.abelian-groups.md) for which any of the following
[logically equivalent](foundation.logical-equivalences.md)
[propositions](foundation.propositions.md) holds:

- its [ring of endomorphisms](group-theory.endomorphism-rings-abelian-groups.md)
  is [a ring extension of `ℚ`](ring-theory.rational-extensions-rings.md), i.e.,
  the [initial ring homomorphism](elementary-number-theory.ring-of-integers.md)
  in its ring of endomorphisms [inverts](ring-theory.localizations-rings.md) the
  [positive integers](elementary-number-theory.positive-integers.md);
- it is a [left module](linear-algebra.left-modules-rings.md) over the
  [ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md);
- it is a [right module](linear-algebra.right-modules-rings.md) over the
  [ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md).

**Note:** Because `ℚ` is a
[discrete field](commutative-algebra.discrete-fields.md), rational modules are
the vector spaces on the
[field of rational numbers](elementary-number-theory.field-of-rational-numbers.md).

## Definitions

### The predicate on abelian groups of being a rational module

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-rational-extension-module-prop-Ab : Prop l
  is-rational-extension-module-prop-Ab =
    is-rational-extension-prop-Ring (endomorphism-ring-Ab A)

  is-rational-extension-module-Ab : UU l
  is-rational-extension-module-Ab =
    type-Prop is-rational-extension-module-prop-Ab

  is-prop-is-rational-extension-module-Ab :
    is-prop is-rational-extension-module-Ab
  is-prop-is-rational-extension-module-Ab =
    is-prop-type-Prop is-rational-extension-module-prop-Ab
```

### The type of rational modules

```agda
Rational-Module : (l : Level) → UU (lsuc l)
Rational-Module l = type-subtype is-rational-extension-module-prop-Ab

module _
  {l : Level} (M : Rational-Module l)
  where

  ab-Rational-Module : Ab l
  ab-Rational-Module = pr1 M

  is-rational-extension-endomorphism-ring-ab-Rational-Module :
    is-rational-extension-Ring (endomorphism-ring-Ab ab-Rational-Module)
  is-rational-extension-endomorphism-ring-ab-Rational-Module = pr2 M

  rational-ring-endomorphism-Rational-Module : Rational-Extension-Ring l
  rational-ring-endomorphism-Rational-Module =
    ( endomorphism-ring-Ab ab-Rational-Module ,
      is-rational-extension-endomorphism-ring-ab-Rational-Module)
```

### The predicate on abelian groups of being a left module on the rationals

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-rational-extension-left-module-Ab : UU l
  is-rational-extension-left-module-Ab =
    hom-Ring ring-ℚ (endomorphism-ring-Ab A)

  is-prop-is-rational-extension-left-module-Ab :
    is-prop is-rational-extension-left-module-Ab
  is-prop-is-rational-extension-left-module-Ab =
    is-prop-has-rational-hom-Ring (endomorphism-ring-Ab A)

  subtype-is-rational-extension-left-module : Prop l
  subtype-is-rational-extension-left-module =
    ( is-rational-extension-left-module-Ab ,
      is-prop-is-rational-extension-left-module-Ab)
```

### The predicate on abelian groups of being a right module on the rationals

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-rational-extension-right-module-Ab : UU l
  is-rational-extension-right-module-Ab =
    hom-Ring ring-ℚ (op-Ring (endomorphism-ring-Ab A))

  is-prop-is-rational-extension-right-module-Ab :
    is-prop is-rational-extension-right-module-Ab
  is-prop-is-rational-extension-right-module-Ab =
    is-prop-has-rational-hom-Ring (op-Ring (endomorphism-ring-Ab A))

  subtype-is-rational-extension-right-module : Prop l
  subtype-is-rational-extension-right-module =
    ( is-rational-extension-right-module-Ab ,
      is-prop-is-rational-extension-right-module-Ab)
```

## Properties

### The type of rational modules is equivalent to the type of left modules over the ring of rational numbers

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-rational-extension-is-rational-extension-left-module-Ab :
    is-rational-extension-left-module-Ab A →
    is-rational-extension-module-Ab A
  is-rational-extension-is-rational-extension-left-module-Ab H =
    is-rational-extension-has-rational-hom-Ring
      ( endomorphism-ring-Ab A)
      ( H)

  is-rational-extension-left-module-is-rational-extension-module-Ab :
    is-rational-extension-module-Ab A →
    is-rational-extension-left-module-Ab A
  is-rational-extension-left-module-is-rational-extension-module-Ab H =
    initial-hom-Rational-Extension-Ring (endomorphism-ring-Ab A , H)

module _
  {l : Level}
  where

  equiv-left-module-Rational-Module :
    left-module-Ring l ring-ℚ ≃ Rational-Module l
  equiv-left-module-Rational-Module =
    equiv-type-subtype
      ( is-prop-is-rational-extension-left-module-Ab)
      ( is-prop-is-rational-extension-module-Ab)
      ( is-rational-extension-is-rational-extension-left-module-Ab)
      ( is-rational-extension-left-module-is-rational-extension-module-Ab)
```

### A rational module is a left module over the ring of rational numbers

```agda
module _
  {l : Level} (M : Rational-Module l)
  where

  left-module-Rational-Module : left-module-Ring l ring-ℚ
  left-module-Rational-Module =
    tot is-rational-extension-left-module-is-rational-extension-module-Ab M
```

### The type of rational modules is equivalent to the type of right modules over the ring of rational numbers

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-rational-extension-is-rational-extension-right-module-Ab :
    is-rational-extension-right-module-Ab A →
    is-rational-extension-module-Ab A
  is-rational-extension-is-rational-extension-right-module-Ab H =
    is-rational-extension-is-rational-extension-op-Ring
      ( endomorphism-ring-Ab A)
      ( is-rational-extension-has-rational-hom-Ring
        ( op-Ring (endomorphism-ring-Ab A))
        ( H))

  is-rational-extension-right-module-is-rational-extension-module-Ab :
    is-rational-extension-module-Ab A →
    is-rational-extension-right-module-Ab A
  is-rational-extension-right-module-is-rational-extension-module-Ab H =
    initial-hom-Rational-Extension-Ring
      ( op-Rational-Extension-Ring (endomorphism-ring-Ab A , H))

module _
  {l : Level}
  where

  equiv-right-module-Rational-Module :
    right-module-Ring l ring-ℚ ≃ Rational-Module l
  equiv-right-module-Rational-Module =
    equiv-type-subtype
      ( is-prop-is-rational-extension-right-module-Ab)
      ( is-prop-is-rational-extension-module-Ab)
      ( is-rational-extension-is-rational-extension-right-module-Ab)
      ( is-rational-extension-right-module-is-rational-extension-module-Ab)
```

### A rational module is a right module over the ring of rational numbers

```agda
module _
  {l : Level} (M : Rational-Module l)
  where

  right-module-Rational-Module : right-module-Ring l ring-ℚ
  right-module-Rational-Module =
    tot is-rational-extension-right-module-is-rational-extension-module-Ab M
```

### An abelian group is a rational module if and only if the actions of positive integers are automorphisms

```agda
module _
  {l : Level} (M : Ab l)
  where

  is-iso-positive-integer-multiple-is-rational-extension-module-Ab :
    is-rational-extension-module-Ab M →
    (k : ℤ⁺) →
    is-iso-Ab M M (hom-integer-multiple-Ab M (int-positive-ℤ k))
  is-iso-positive-integer-multiple-is-rational-extension-module-Ab H k =
    tr
      ( is-iso-Ab M M)
      ( htpy-initial-hom-integer-multiple-endomorphism-ring-Ab
        ( M)
        ( int-positive-ℤ k))
      ( ind-Σ
        ( is-rational-extension-endomorphism-ring-ab-Rational-Module (M , H))
        ( k))

  is-rational-extension-left-module-is-iso-positive-integer-multiple-Ab :
    ((k : ℤ⁺) → is-iso-Ab M M (hom-integer-multiple-Ab M (int-positive-ℤ k))) →
    is-rational-extension-module-Ab M
  is-rational-extension-left-module-is-iso-positive-integer-multiple-Ab
    H k k>0 =
    inv-tr
      ( is-invertible-element-Ring (endomorphism-ring-Ab M))
      ( htpy-initial-hom-integer-multiple-endomorphism-ring-Ab M k)
      ( ev-pair H k k>0)
```

## External links

- [rational vector space](https://ncatlab.org/nlab/show/rational+vector+space)
  at $n$Lab
