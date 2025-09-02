# The minimum of finite families of real numbers

```agda
module real-numbers.minimum-finite-families-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences

open import logic.functoriality-existential-quantification

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.lower-bounds-large-posets
open import order-theory.meet-semilattices
open import order-theory.meets-finite-families-meet-semilattices

open import real-numbers.addition-real-numbers
open import real-numbers.binary-minimum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.infima-families-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.strict-inequality-real-numbers

open import univalent-combinatorics.counting
open import univalent-combinatorics.inhabited-finite-types
open import univalent-combinatorics.standard-finite-types
open import real-numbers.maximum-finite-families-real-numbers
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="inhabited finite family, Dedekind real numbers" Agda=min-finite-family-ℝ WD="minimum" WDID=Q10578722}}
of a family of [Dedekind real numbers](real-numbers.dedekind-real-numbers.md)
indexed by an
[inhabited finite type](univalent-combinatorics.inhabited-finite-types.md) is
their
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md).

## Definition

### The minimum of a nonempty sequence of real numbers

```agda
module _
  {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n))
  where

  opaque
    min-fin-sequence-ℝ : ℝ l
    min-fin-sequence-ℝ = neg-ℝ (max-fin-sequence-ℝ n (neg-ℝ ∘ x))
```

### The minimum of an inhabited finite family of real numbers

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (f : type-Inhabited-Finite-Type I → ℝ l2)
  where

  opaque
    min-finite-family-ℝ : ℝ l2
    min-finite-family-ℝ = neg-ℝ (max-finite-family-ℝ I (neg-ℝ ∘ f))
```

## Properties

### The minimum of a sequence is its infimum

```agda
opaque
  unfolding min-fin-sequence-ℝ

  is-infimum-min-fin-sequence-ℝ :
    {l : Level} (n : ℕ) (x : fin-sequence (ℝ l) (succ-ℕ n)) →
    is-infimum-family-ℝ x (min-fin-sequence-ℝ n x)
  is-infimum-min-fin-sequence-ℝ n x =
    is-infimum-neg-supremum-neg-family-ℝ
      ( x)
      ( max-fin-sequence-ℝ n (neg-ℝ ∘ x))
      ( is-supremum-max-fin-sequence-ℝ n (neg-ℝ ∘ x))
```

### The minimum of a finite family is its infimum

```agda
module _
  {l1 l2 : Level} (I : Inhabited-Finite-Type l1)
  (x : type-Inhabited-Finite-Type I → ℝ l2)
  where

  opaque
    unfolding min-finite-family-ℝ

    is-infimum-min-finite-family-ℝ :
      is-infimum-family-ℝ x (min-finite-family-ℝ I x)
    is-infimum-min-finite-family-ℝ =
      is-infimum-neg-supremum-neg-family-ℝ
        ( x)
        ( max-finite-family-ℝ I (neg-ℝ ∘ x))
        ( is-supremum-max-finite-family-ℝ I (neg-ℝ ∘ x))
```
