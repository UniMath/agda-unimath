# Convolution of sequences in commutative rings

```agda
module commutative-algebra.convolution-sequences-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings
open import commutative-algebra.convolution-sequences-commutative-semirings
open import commutative-algebra.function-commutative-rings

open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unital-binary-operations
open import foundation.universe-levels

open import group-theory.abelian-groups
open import group-theory.semigroups

open import lists.sequences

open import ring-theory.convolution-sequences-rings
open import ring-theory.rings
open import ring-theory.sequences-rings

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "convolution" WD="convolution" Disambiguation="ring of sequences in commutative rings" Agda=convolution-sequence-Commutative-Ring WDID=Q210857}}
[commutative ring](commutative-algebra.commutative-rings.md)
[sequences](ring-theory.sequences-rings.md) in a commutative ring is the
[ring](ring-theory.rings.md) of sequences with pointwise addition and
[convolution product](ring-theory.convolution-sequences-rings.md).

## Definitions

### The commutative ring of sequences in a commutative ring under convolution

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  ring-convolution-sequence-Commutative-Ring : Ring l
  ring-convolution-sequence-Commutative-Ring =
    convolution-sequence-Ring (ring-Commutative-Ring R)

  is-commutative-ring-convolution-sequence-Commutative-Ring :
    is-commutative-Ring ring-convolution-sequence-Commutative-Ring
  is-commutative-ring-convolution-sequence-Commutative-Ring =
    is-commutative-semiring-convolution-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  convolution-sequence-Commutative-Ring : Commutative-Ring l
  convolution-sequence-Commutative-Ring =
    ( ring-convolution-sequence-Commutative-Ring ,
      is-commutative-ring-convolution-sequence-Commutative-Ring)

  zero-convolution-sequence-Commutative-Ring :
    type-sequence-Ring (ring-Commutative-Ring R)
  zero-convolution-sequence-Commutative-Ring =
    zero-Commutative-Ring convolution-sequence-Commutative-Ring

  one-convolution-sequence-Commutative-Ring :
    type-sequence-Ring (ring-Commutative-Ring R)
  one-convolution-sequence-Commutative-Ring =
    one-Commutative-Ring convolution-sequence-Commutative-Ring
```
