# Tagged partitions of closed intervals of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.tagged-partitions-closed-intervals-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.finite-sequences-of-types

open import real-numbers.closed-intervals-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.large-poset-closed-intervals-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.partitions-closed-intervals-real-numbers

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A
{{#concept "tagged partition" Disambiguation="of a closed interval in the real numbers" Agda=tagged-partition-closed-interval-ℝ}}
of a [closed interval](real-numbers.closed-intervals-real-numbers.md) `[a, b]`
in the [real numbers](real-numbers.dedekind-real-numbers.md) is a
[partition](real-numbers.partitions-closed-intervals-real-numbers.md) of
`[a, b]` together with an element of each interval in the partition.

## Definition

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  where

  type-tags-partition-closed-interval-ℝ :
    (p : partition-closed-interval-ℝ [a,b]) →
    fin-sequence
      ( UU (lsuc l))
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
  type-tags-partition-closed-interval-ℝ p =
    type-closed-interval-ℝ l ∘
    fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p

  tags-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b] → UU (lsuc l)
  tags-partition-closed-interval-ℝ p =
    Π-fin-sequence
      ( pred-length-partition-closed-interval-ℝ [a,b] p)
      ( type-tags-partition-closed-interval-ℝ p)

  tagged-partition-closed-interval-ℝ : UU (lsuc l)
  tagged-partition-closed-interval-ℝ =
    Σ ( partition-closed-interval-ℝ [a,b])
      ( tags-partition-closed-interval-ℝ)
```

## Properties

### Properties inherited from partitions

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  (tp@(p , t) : tagged-partition-closed-interval-ℝ [a,b])
  where

  pred-length-tagged-partition-closed-interval-ℝ : ℕ
  pred-length-tagged-partition-closed-interval-ℝ =
    pred-length-partition-closed-interval-ℝ [a,b] p

  partition-tagged-partition-closed-interval-ℝ :
    partition-closed-interval-ℝ [a,b]
  partition-tagged-partition-closed-interval-ℝ = p

  tags-tagged-partition-closed-interval-ℝ :
    tags-partition-closed-interval-ℝ
      ( [a,b])
      ( partition-tagged-partition-closed-interval-ℝ)
  tags-tagged-partition-closed-interval-ℝ = t

  real-tags-tagged-partition-closed-interval-ℝ :
    fin-sequence
      ( ℝ l)
      ( pred-length-tagged-partition-closed-interval-ℝ)
  real-tags-tagged-partition-closed-interval-ℝ =
    pr1 ∘ tags-tagged-partition-closed-interval-ℝ

  mesh-tagged-partition-closed-interval-ℝ : ℝ⁰⁺ l
  mesh-tagged-partition-closed-interval-ℝ =
    mesh-partition-closed-interval-ℝ [a,b] p

  abstract
    is-in-interval-real-tags-tagged-partition-closed-interval-ℝ :
      (i : Fin pred-length-tagged-partition-closed-interval-ℝ) →
      is-in-closed-interval-ℝ
        ( [a,b])
        ( real-tags-tagged-partition-closed-interval-ℝ i)
    is-in-interval-real-tags-tagged-partition-closed-interval-ℝ i =
      let
        [aᵢ,bᵢ] =
          fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p i
        (t , t∈[aᵢ,bᵢ]) = tags-tagged-partition-closed-interval-ℝ i
      in
        leq-subtype-leq-closed-interval-ℝ
          ( [aᵢ,bᵢ])
          ( [a,b])
          ( leq-fin-sequence-closed-interval-partition-closed-interval-ℝ
            ( [a,b])
            ( p)
            ( i))
          ( t)
          ( t∈[aᵢ,bᵢ])

  fin-sequence-tags-elements-tagged-partition-closed-interval-ℝ :
    fin-sequence
      ( type-closed-interval-ℝ l [a,b])
      ( pred-length-tagged-partition-closed-interval-ℝ)
  fin-sequence-tags-elements-tagged-partition-closed-interval-ℝ i =
    ( real-tags-tagged-partition-closed-interval-ℝ i ,
      is-in-interval-real-tags-tagged-partition-closed-interval-ℝ i)
```

### Tagging partitions with their lower or upper bounds

```agda
module _
  {l : Level}
  ([a,b] : closed-interval-ℝ l l)
  (p : partition-closed-interval-ℝ [a,b])
  where

  tag-lower-bounds-partition-closed-interval-ℝ :
    tagged-partition-closed-interval-ℝ [a,b]
  tag-lower-bounds-partition-closed-interval-ℝ =
    ( p ,
      ( lower-bound-type-closed-interval-ℝ ∘
        fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p))

  tag-upper-bounds-partition-closed-interval-ℝ :
    tagged-partition-closed-interval-ℝ [a,b]
  tag-upper-bounds-partition-closed-interval-ℝ =
    ( p ,
      ( upper-bound-type-closed-interval-ℝ ∘
        fin-sequence-closed-interval-partition-closed-interval-ℝ [a,b] p))
```
