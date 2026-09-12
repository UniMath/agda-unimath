# Convolution of sequences in commutative semirings

```agda
module commutative-algebra.convolution-sequences-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import ring-theory.convolution-sequences-semirings
open import ring-theory.semirings
open import ring-theory.sequences-semirings
```

</details>

## Idea

The
{{#concept "convolution" WD="convolution" Disambiguation="of sequences in commutative semirings" Agda=convolution-sequence-Commutative-Semiring WDID=Q210857}}
of two [sequences](lists.sequences.md) `aₙ` and `bₙ` of elements in a
[commutative semiring](commutative-algebra.commutative-semirings.md) is the new
sequence

```text
  cₙ = ∑_{0 ≤ i ≤ n} aₙ bₙ₋ᵢ
```

With pairwise addition, this operation forms a new commutative semiring.

## Definitions

### The commutative semiring of sequences in a commutative semiring under convolution

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  semiring-convolution-sequence-Commutative-Semiring : Semiring l
  semiring-convolution-sequence-Commutative-Semiring =
    convolution-sequence-Semiring (semiring-Commutative-Semiring R)

  is-commutative-semiring-convolution-sequence-Commutative-Semiring :
    is-commutative-Semiring semiring-convolution-sequence-Commutative-Semiring
  is-commutative-semiring-convolution-sequence-Commutative-Semiring a b =
    commute-mul-convolution-sequence-Semiring
      ( semiring-Commutative-Semiring R)
      ( a)
      ( b)
      ( λ i j → commutative-mul-Commutative-Semiring R _ _)

  convolution-sequence-Commutative-Semiring : Commutative-Semiring l
  convolution-sequence-Commutative-Semiring =
    ( semiring-convolution-sequence-Commutative-Semiring ,
      is-commutative-semiring-convolution-sequence-Commutative-Semiring)

  zero-convolution-sequence-Commutative-Semiring :
    type-sequence-Semiring (semiring-Commutative-Semiring R)
  zero-convolution-sequence-Commutative-Semiring =
    zero-Commutative-Semiring convolution-sequence-Commutative-Semiring

  one-convolution-sequence-Commutative-Semiring :
    type-sequence-Semiring (semiring-Commutative-Semiring R)
  one-convolution-sequence-Commutative-Semiring =
    one-Commutative-Semiring convolution-sequence-Commutative-Semiring
```
