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

open import ring-theory.rings

open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "convolution" WD="convolution" Disambiguation="of sequences in commutative rings" Agda=convolution-sequence-Commutative-Ring WDID=Q210857}}
of two [sequences](lists.sequences.md) `aₙ` and `bₙ` of elements in a
[commutative ring](commutative-algebra.commutative-rings.md) is the new sequence

```text
  cₙ = ∑_{0 ≤ i ≤ n} aₙ bₙ₋ᵢ
```

With pairwise addition, this operation forms a new commutative ring.

## Definition

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  convolution-sequence-Commutative-Ring :
    sequence (type-Commutative-Ring R) →
    sequence (type-Commutative-Ring R) →
    sequence (type-Commutative-Ring R)
  convolution-sequence-Commutative-Ring =
    convolution-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)
```

## Properties

### Commutativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    commutative-convolution-sequence-Commutative-Ring :
      (a b : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R a b ＝
      convolution-sequence-Commutative-Ring R b a
    commutative-convolution-sequence-Commutative-Ring =
      commutative-convolution-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)
```

### Unit laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  unit-convolution-sequence-Commutative-Ring :
    sequence (type-Commutative-Ring R)
  unit-convolution-sequence-Commutative-Ring =
    unit-convolution-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  abstract
    left-unit-law-convolution-sequence-Commutative-Ring :
      (a : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( unit-convolution-sequence-Commutative-Ring)
        ( a)
        ＝ a
    left-unit-law-convolution-sequence-Commutative-Ring =
      left-unit-law-convolution-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)

    right-unit-law-convolution-sequence-Commutative-Ring :
      (a : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( a)
        ( unit-convolution-sequence-Commutative-Ring)
        ＝ a
    right-unit-law-convolution-sequence-Commutative-Ring =
      right-unit-law-convolution-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)
```

### Associativity

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    associative-convolution-sequence-Commutative-Ring :
      (a b c : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( convolution-sequence-Commutative-Ring R a b)
        ( c) ＝
      convolution-sequence-Commutative-Ring R
        ( a)
        ( convolution-sequence-Commutative-Ring R b c)
    associative-convolution-sequence-Commutative-Ring =
      associative-convolution-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)
```

### Zero laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    left-zero-law-convolution-sequence-Commutative-Ring :
      (a : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( zero-function-Commutative-Ring R ℕ)
        ( a) ＝
      zero-function-Commutative-Ring R ℕ
    left-zero-law-convolution-sequence-Commutative-Ring =
      left-zero-law-convolution-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)

    right-zero-law-convolution-sequence-Commutative-Ring :
      (a : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( a)
        ( zero-function-Commutative-Ring R ℕ) ＝
      zero-function-Commutative-Ring R ℕ
    right-zero-law-convolution-sequence-Commutative-Ring =
      right-zero-law-convolution-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)
```

### Distributivity laws

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  abstract
    left-distributive-convolution-add-sequence-Commutative-Ring :
      (a b c : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( a)
        ( add-function-Commutative-Ring R ℕ b c) ＝
      add-function-Commutative-Ring R ℕ
        ( convolution-sequence-Commutative-Ring R a b)
        ( convolution-sequence-Commutative-Ring R a c)
    left-distributive-convolution-add-sequence-Commutative-Ring =
      left-distributive-convolution-add-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)

    right-distributive-convolution-add-sequence-Commutative-Ring :
      (a b c : sequence (type-Commutative-Ring R)) →
      convolution-sequence-Commutative-Ring R
        ( add-function-Commutative-Ring R ℕ a b)
        ( c) ＝
      add-function-Commutative-Ring R ℕ
        ( convolution-sequence-Commutative-Ring R a c)
        ( convolution-sequence-Commutative-Ring R b c)
    right-distributive-convolution-add-sequence-Commutative-Ring =
      right-distributive-convolution-add-sequence-Commutative-Semiring
        ( commutative-semiring-Commutative-Ring R)
```

### Commutative ring of sequences of elements of commutative rings under convolution

```agda
module _
  {l : Level} (R : Commutative-Ring l)
  where

  additive-ab-sequence-Commutative-Ring : Ab l
  additive-ab-sequence-Commutative-Ring = ab-function-Commutative-Ring R ℕ

  has-associative-mul-convolution-sequence-Commutative-Ring :
    has-associative-mul (sequence (type-Commutative-Ring R))
  has-associative-mul-convolution-sequence-Commutative-Ring =
    has-associative-mul-convolution-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  is-unital-convolution-sequence-Commutative-Ring :
    is-unital (convolution-sequence-Commutative-Ring R)
  is-unital-convolution-sequence-Commutative-Ring =
    is-unital-convolution-sequence-Commutative-Semiring
      ( commutative-semiring-Commutative-Ring R)

  has-mul-convolution-additive-ab-sequence-Commutative-Ring :
    has-mul-Ab additive-ab-sequence-Commutative-Ring
  pr1 has-mul-convolution-additive-ab-sequence-Commutative-Ring =
    has-associative-mul-convolution-sequence-Commutative-Ring
  pr1 (pr2 has-mul-convolution-additive-ab-sequence-Commutative-Ring) =
    is-unital-convolution-sequence-Commutative-Ring
  pr1 (pr2 (pr2 has-mul-convolution-additive-ab-sequence-Commutative-Ring)) =
    left-distributive-convolution-add-sequence-Commutative-Ring R
  pr2 (pr2 (pr2 has-mul-convolution-additive-ab-sequence-Commutative-Ring)) =
    right-distributive-convolution-add-sequence-Commutative-Ring R

  ring-convolution-sequence-Commutative-Ring : Ring l
  pr1 ring-convolution-sequence-Commutative-Ring =
    additive-ab-sequence-Commutative-Ring
  pr2 ring-convolution-sequence-Commutative-Ring =
    has-mul-convolution-additive-ab-sequence-Commutative-Ring

  commutative-ring-convolution-sequence-Commutative-Ring : Commutative-Ring l
  pr1 commutative-ring-convolution-sequence-Commutative-Ring =
    ring-convolution-sequence-Commutative-Ring
  pr2 commutative-ring-convolution-sequence-Commutative-Ring =
    commutative-convolution-sequence-Commutative-Ring R
```
