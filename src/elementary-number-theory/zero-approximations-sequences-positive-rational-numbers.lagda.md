# Sequences of positive rational numbers approximating zero

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.zero-approximations-sequences-positive-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.additive-group-of-rational-numbers
open import elementary-number-theory.arithmetic-sequences-positive-rational-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.multiplicative-group-of-positive-rational-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.constant-maps
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-subtypes
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sequences
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.arithmetic-sequences-semigroups
open import group-theory.powers-of-elements-monoids

open import order-theory.sequences-preorders
open import order-theory.strictly-increasing-sequences-strictly-preordered-sets
```

</details>

## Idea

A [sequence](foundation.sequences.md) `u` of
[positive rational numbers](elementary-number-theory.positive-rational-numbers.md)
is a
{{#concept "zero approximation" Disambiguation="sequence of positive rational numbers" Agda=zero-approximation-sequence-ℚ⁺}}
if there exists a map `m : ℚ⁺ → ℕ` such that `u n < ε` in ℚ⁺ whenever `m ε ≤ n`
in ℕ.

## Definitions

### The predicate of being a zero approximation sequence

```agda
module _
  (u : sequence ℚ⁺)
  where

  is-modulus-zero-approximation-prop-sequence-ℚ⁺ : (ℚ⁺ → ℕ) → Prop lzero
  is-modulus-zero-approximation-prop-sequence-ℚ⁺ m =
    Π-Prop
      ( ℚ⁺)
      ( λ ε →
        Π-Prop
          ( ℕ)
          ( λ n →
            leq-ℕ-Prop (m ε) n ⇒
            le-prop-ℚ⁺ (u n) ε))

  is-modulus-zero-approximation-sequence-ℚ⁺ : (ℚ⁺ → ℕ) → UU lzero
  is-modulus-zero-approximation-sequence-ℚ⁺ m =
    type-Prop (is-modulus-zero-approximation-prop-sequence-ℚ⁺ m)

  modulus-zero-approximation-sequence-ℚ⁺ : UU lzero
  modulus-zero-approximation-sequence-ℚ⁺ =
    type-subtype is-modulus-zero-approximation-prop-sequence-ℚ⁺

  modulus-modulus-zero-approximation-sequence-ℚ⁺ :
    modulus-zero-approximation-sequence-ℚ⁺ → ℚ⁺ → ℕ
  modulus-modulus-zero-approximation-sequence-ℚ⁺ = pr1

  is-modulus-modulus-zero-approximation-sequence-ℚ⁺ :
    (m : modulus-zero-approximation-sequence-ℚ⁺) →
    is-modulus-zero-approximation-sequence-ℚ⁺
      ( modulus-modulus-zero-approximation-sequence-ℚ⁺ m)
  is-modulus-modulus-zero-approximation-sequence-ℚ⁺ = pr2

  is-zero-approximation-prop-sequence-ℚ⁺ : Prop lzero
  is-zero-approximation-prop-sequence-ℚ⁺ =
    is-inhabited-subtype-Prop is-modulus-zero-approximation-prop-sequence-ℚ⁺

  is-zero-approximation-sequence-ℚ⁺ : UU lzero
  is-zero-approximation-sequence-ℚ⁺ =
    type-Prop is-zero-approximation-prop-sequence-ℚ⁺
```

### Zero approximation sequences in ℚ⁺

```agda
zero-approximation-sequence-ℚ⁺ : UU lzero
zero-approximation-sequence-ℚ⁺ =
  type-subtype is-zero-approximation-prop-sequence-ℚ⁺

module _
  (u : zero-approximation-sequence-ℚ⁺)
  where

  seq-zero-approximation-sequence-ℚ⁺ : sequence ℚ⁺
  seq-zero-approximation-sequence-ℚ⁺ = pr1 u

  is-zero-approximation-seq-zero-approximation-sequence-ℚ⁺ :
    is-zero-approximation-sequence-ℚ⁺ seq-zero-approximation-sequence-ℚ⁺
  is-zero-approximation-seq-zero-approximation-sequence-ℚ⁺ = pr2 u
```

## Properties

### Two zero approximations with the same values are equal

```agda
module _
  (u v : zero-approximation-sequence-ℚ⁺)
  where

  eq-htpy-seq-zero-approximation-sequence-ℚ⁺ :
    ( seq-zero-approximation-sequence-ℚ⁺ u ~
      seq-zero-approximation-sequence-ℚ⁺ v) →
    u ＝ v
  eq-htpy-seq-zero-approximation-sequence-ℚ⁺ H =
    eq-type-subtype
      ( is-zero-approximation-prop-sequence-ℚ⁺)
      ( eq-htpy H)
```

### The suptype of zero approximations is downward closed

Given to sequences `0 < u ≤ v`, if `v` is a zero-approximation, so is `u`.

```agda
module _
  (u v : sequence ℚ⁺) (I : leq-sequence-Preorder preorder-ℚ⁺ u v)
  where

  modulus-leq-modulus-zero-approximation-sequence-ℚ⁺ :
    modulus-zero-approximation-sequence-ℚ⁺ v →
    modulus-zero-approximation-sequence-ℚ⁺ u
  modulus-leq-modulus-zero-approximation-sequence-ℚ⁺ =
    tot
      ( λ N Mu ε n J →
        concatenate-leq-le-ℚ
          ( rational-ℚ⁺ (u n))
          ( rational-ℚ⁺ (v n))
          ( rational-ℚ⁺ ε)
          ( I n)
          ( Mu ε n J))

  is-downward-closed-zero-approximation-sequence-ℚ⁺ :
    is-zero-approximation-sequence-ℚ⁺ v →
    is-zero-approximation-sequence-ℚ⁺ u
  is-downward-closed-zero-approximation-sequence-ℚ⁺ =
    map-is-inhabited modulus-leq-modulus-zero-approximation-sequence-ℚ⁺
```

### The sum of two zero approximations is a zero approximation

```agda
module _
  (u v : zero-approximation-sequence-ℚ⁺)
  where

  seq-add-zero-approximations-sequence-ℚ⁺ : sequence ℚ⁺
  seq-add-zero-approximations-sequence-ℚ⁺ n =
    add-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ u n)
      ( seq-zero-approximation-sequence-ℚ⁺ v n)

  modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ :
    modulus-zero-approximation-sequence-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ u) →
    modulus-zero-approximation-sequence-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ v) →
    ℚ⁺ → ℕ
  modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv ε =
    max-ℕ
      ( modulus-modulus-zero-approximation-sequence-ℚ⁺
        ( seq-zero-approximation-sequence-ℚ⁺ u)
        ( Mu)
        ( left-summand-split-ℚ⁺ ε))
      ( modulus-modulus-zero-approximation-sequence-ℚ⁺
        ( seq-zero-approximation-sequence-ℚ⁺ v)
        ( Mv)
        ( right-summand-split-ℚ⁺ ε))

  is-modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ :
    ( Mu : modulus-zero-approximation-sequence-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ u)) →
    ( Mv : modulus-zero-approximation-sequence-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ v)) →
    ( is-modulus-zero-approximation-sequence-ℚ⁺
      ( seq-add-zero-approximations-sequence-ℚ⁺)
      ( modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv))
  is-modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv ε n I =
    tr
      ( le-ℚ⁺ (seq-add-zero-approximations-sequence-ℚ⁺ n))
      ( eq-add-split-ℚ⁺ ε)
      ( preserves-le-add-ℚ
        { rational-ℚ⁺ (seq-zero-approximation-sequence-ℚ⁺ u n)}
        { rational-ℚ⁺ (left-summand-split-ℚ⁺ ε)}
        { rational-ℚ⁺ (seq-zero-approximation-sequence-ℚ⁺ v n)}
        { rational-ℚ⁺ (right-summand-split-ℚ⁺ ε)}
        ( is-modulus-modulus-zero-approximation-sequence-ℚ⁺
          ( seq-zero-approximation-sequence-ℚ⁺ u)
          ( Mu)
          ( left-summand-split-ℚ⁺ ε)
          ( n)
          ( leq-left-leq-max-ℕ
            ( n)
            ( modulus-modulus-zero-approximation-sequence-ℚ⁺
              ( seq-zero-approximation-sequence-ℚ⁺ u)
              ( Mu)
              ( left-summand-split-ℚ⁺ ε))
            ( modulus-modulus-zero-approximation-sequence-ℚ⁺
              ( seq-zero-approximation-sequence-ℚ⁺ v)
              ( Mv)
              ( right-summand-split-ℚ⁺ ε))
            ( I)))
        ( is-modulus-modulus-zero-approximation-sequence-ℚ⁺
          ( seq-zero-approximation-sequence-ℚ⁺ v)
          ( Mv)
          ( right-summand-split-ℚ⁺ ε)
          ( n)
          ( leq-right-leq-max-ℕ
            ( n)
            ( modulus-modulus-zero-approximation-sequence-ℚ⁺
              ( seq-zero-approximation-sequence-ℚ⁺ u)
              ( Mu)
              ( left-summand-split-ℚ⁺ ε))
            ( modulus-modulus-zero-approximation-sequence-ℚ⁺
              ( seq-zero-approximation-sequence-ℚ⁺ v)
              ( Mv)
              ( right-summand-split-ℚ⁺ ε))
            ( I))))

  modulus-add-modulus-zero-approximations-sequence-ℚ⁺ :
    modulus-zero-approximation-sequence-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ u) →
    modulus-zero-approximation-sequence-ℚ⁺
      ( seq-zero-approximation-sequence-ℚ⁺ v) →
    modulus-zero-approximation-sequence-ℚ⁺
      seq-add-zero-approximations-sequence-ℚ⁺
  modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv =
    modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv ,
    is-modulus-modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv

  is-zero-approximation-seq-add-zero-approximation-sequence-ℚ⁺ :
    is-zero-approximation-sequence-ℚ⁺ seq-add-zero-approximations-sequence-ℚ⁺
  is-zero-approximation-seq-add-zero-approximation-sequence-ℚ⁺ =
    rec-trunc-Prop
      ( is-zero-approximation-prop-sequence-ℚ⁺
        seq-add-zero-approximations-sequence-ℚ⁺)
      ( λ Mv →
        rec-trunc-Prop
          ( is-zero-approximation-prop-sequence-ℚ⁺
            ( seq-add-zero-approximations-sequence-ℚ⁺))
          ( λ Mu →
            unit-trunc-Prop
              ( modulus-add-modulus-zero-approximations-sequence-ℚ⁺ Mu Mv))
          ( is-zero-approximation-seq-zero-approximation-sequence-ℚ⁺ u))
      ( is-zero-approximation-seq-zero-approximation-sequence-ℚ⁺ v)

  add-zero-approximation-sequence-ℚ⁺ : zero-approximation-sequence-ℚ⁺
  add-zero-approximation-sequence-ℚ⁺ =
    seq-add-zero-approximations-sequence-ℚ⁺ ,
    is-zero-approximation-seq-add-zero-approximation-sequence-ℚ⁺
```

### Addition of zero approximations is associative

```agda
associative-add-zero-approximation-sequence-ℚ⁺ :
  (u v w : zero-approximation-sequence-ℚ⁺) →
  (add-zero-approximation-sequence-ℚ⁺
    ( add-zero-approximation-sequence-ℚ⁺ u v)
    ( w)) ＝
  (add-zero-approximation-sequence-ℚ⁺
    ( u)
    ( add-zero-approximation-sequence-ℚ⁺ v w))
associative-add-zero-approximation-sequence-ℚ⁺ u v w =
  eq-htpy-seq-zero-approximation-sequence-ℚ⁺
    ( add-zero-approximation-sequence-ℚ⁺
      ( add-zero-approximation-sequence-ℚ⁺ u v)
      ( w))
    ( add-zero-approximation-sequence-ℚ⁺
      ( u)
      ( add-zero-approximation-sequence-ℚ⁺ v w))
    ( λ n →
      associative-add-ℚ⁺
        ( seq-zero-approximation-sequence-ℚ⁺ u n)
        ( seq-zero-approximation-sequence-ℚ⁺ v n)
        ( seq-zero-approximation-sequence-ℚ⁺ w n))
```
