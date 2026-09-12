# Convolution of sequences in rings

```agda
module ring-theory.convolution-sequences-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.semigroups

open import ring-theory.convolution-sequences-semirings
open import ring-theory.rings
open import ring-theory.semirings
open import ring-theory.sequences-rings
```

</details>

## Idea

The
{{#concept "convolution product" WD="convolution" Disambiguation="of sequences in rings" Agda=mul-convolution-sequence-Ring WDID=Q210857}}
of two [sequences](ring-theory.sequences-rings.md) `aₙ` and `bₙ` in a
[ring](ring-theory.rings.md) is the sequence `c = a ⋆ b` defined by:

```text
  cₙ = ∑_{0 ≤ i ≤ n} aₙ bₙ₋ᵢ
```

With pointwise addition, this forms the
{{#concept "convolution ring" Disambiguation="of sequences in rings" Agda=convolution-sequence-Ring}}
of sequences in a ring.

## Definition

### The ring of sequences in a ring under convolution

```agda
module _
  {l : Level} (R : Ring l)
  where

  mul-convolution-sequence-Ring :
    type-sequence-Ring R →
    type-sequence-Ring R →
    type-sequence-Ring R
  mul-convolution-sequence-Ring =
    mul-convolution-sequence-Semiring (semiring-Ring R)

  has-associative-mul-convolution-sequence-Ring :
    has-associative-mul (type-sequence-Ring R)
  has-associative-mul-convolution-sequence-Ring =
    ( mul-convolution-sequence-Semiring (semiring-Ring R) ,
      associative-mul-convolution-sequence-Semiring (semiring-Ring R))

  is-unital-mul-convolution-sequence-Ring :
    is-unital mul-convolution-sequence-Ring
  is-unital-mul-convolution-sequence-Ring =
    ( unit-convolution-sequence-Semiring (semiring-Ring R) ,
      left-unit-law-convolution-sequence-Semiring (semiring-Ring R) ,
      right-unit-law-convolution-sequence-Semiring (semiring-Ring R))

  convolution-sequence-Ring : Ring l
  convolution-sequence-Ring =
    ( ab-sequence-Ring R ,
      has-associative-mul-convolution-sequence-Ring ,
      is-unital-mul-convolution-sequence-Ring ,
      left-distributive-convolution-add-sequence-Semiring (semiring-Ring R) ,
      right-distributive-convolution-add-sequence-Semiring (semiring-Ring R))
```
