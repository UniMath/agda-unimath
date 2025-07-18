# Left rational modules

```agda
module linear-algebra.left-rational-modules where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-integers
open import elementary-number-theory.ring-of-rational-numbers

open import foundation.dependent-pair-types
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

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.rational-rings
open import ring-theory.rings
```

</details>

## Idea

A {{concept "rational left module" Agda=left-Rational-Module}} is a
[left module](linear-algebra.left-modules-rings.md) over the
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md).

An [abelian group](group-theory.abelian-groups.md) is a **left rational module**
if and only if its
[ring of endomorphisms](group-theory.endomorphism-rings-abelian-groups.md) is
[rational](ring-theory.rational-rings.md).

## Definitions

### The property of being a left rational module

```agda
module _
  {l : Level} (A : Ab l)
  where

  is-rational-left-module-prop-Ab : Prop l
  is-rational-left-module-prop-Ab =
    has-rational-hom-prop-Ring (endomorphism-ring-Ab A)

  is-rational-left-module-Ab : UU l
  is-rational-left-module-Ab =
    type-Prop is-rational-left-module-prop-Ab

  is-prop-is-rational-left-module-Ab :
    is-prop is-rational-left-module-Ab
  is-prop-is-rational-left-module-Ab =
    is-prop-type-Prop is-rational-left-module-prop-Ab
```

### The type of left rational modules

```agda
left-Rational-Module : (l : Level) → UU (lsuc l)
left-Rational-Module l =
  Σ (Ab l) is-rational-left-module-Ab

module _
  {l : Level} (M : left-Rational-Module l)
  where

  left-module-left-Rational-Module : left-module-Ring l ring-ℚ
  left-module-left-Rational-Module = M
```

## Properties

### An abelian group is a left rational module if and only if its ring of endomorphisms is rational

```agda
module _
  {l : Level} (M : Ab l)
  where

  is-rational-left-module-is-rational-ring-endo-Ab :
    is-rational-Ring (endomorphism-ring-Ab M) →
    is-rational-left-module-Ab M
  is-rational-left-module-is-rational-ring-endo-Ab =
    has-rational-hom-is-rational-Ring (endomorphism-ring-Ab M)

  is-rational-endo-ring-is-rational-left-module-Ab :
    is-rational-left-module-Ab M →
    is-rational-Ring (endomorphism-ring-Ab M)
  is-rational-endo-ring-is-rational-left-module-Ab =
    is-rational-has-rational-hom-Ring (endomorphism-ring-Ab M)
```

### An abelian group `A` is a left rational module if and only if for any `k : ℤ⁺` the map `x ↦ k x` is an isomorphism

```agda
module _
  {l : Level} (M : Ab l)
  where

  is-iso-positive-integer-multiple-is-rational-left-module-Ab :
    is-rational-left-module-Ab M →
    (k : ℤ⁺) →
    is-iso-Ab M M (hom-integer-multiple-Ab M (int-positive-ℤ k))
  is-iso-positive-integer-multiple-is-rational-left-module-Ab H k =
    tr
      ( is-iso-Ab M M)
      ( htpy-initial-hom-integer-multiple-endomorphism-ring-Ab
        ( M)
        ( int-positive-ℤ k))
      ( ind-Σ
        ( is-rational-endo-ring-is-rational-left-module-Ab M H)
        ( k))

  is-rational-left-module-is-iso-positive-integer-multiple-Ab :
    ((k : ℤ⁺) → is-iso-Ab M M (hom-integer-multiple-Ab M (int-positive-ℤ k))) →
    is-rational-left-module-Ab M
  is-rational-left-module-is-iso-positive-integer-multiple-Ab H =
    is-rational-left-module-is-rational-ring-endo-Ab
      ( M)
      ( λ k k>0 →
        inv-tr
          ( is-invertible-element-Ring (endomorphism-ring-Ab M))
          ( htpy-initial-hom-integer-multiple-endomorphism-ring-Ab
            ( M)
            ( k))
        ( ev-pair H k k>0))
```
