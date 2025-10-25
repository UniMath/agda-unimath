# Decidability of dependents sums over increasing binary sequences

```agda
module set-theory.decidable-dependent-pair-types-over-increasing-binary-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.booleans
open import foundation.constant-maps
open import foundation.coproduct-types
open import foundation.decidable-type-families
open import foundation.dependent-pair-types
open import foundation.double-negation
open import foundation.double-negation-stable-equality
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.homotopies
open import foundation.inequality-booleans
open import foundation.injective-maps
open import foundation.logical-operations-booleans
open import foundation.maybe
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.tight-apartness-relations
open import foundation.transport-along-identifications
open import foundation.types-with-decidable-dependent-pair-types
open import foundation.types-with-decidable-dependent-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types

open import order-theory.order-preserving-maps-posets

open import set-theory.cantor-space
open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.strict-lower-bounds-increasing-binary-sequences
```

</details>

## Idea

[Dependent sums](foundation.dependent-pair-types.md) of
[decidable types](foundation.decidable-types.md) over
[increasing binary sequences](set-theory.increasing-binary-sequences.md) are
decidable. {{#cite Esc13}}

## Proof

We prove that the type of increasing binary sequences pointedly has decidable
dependent sums, from which the main result is an easy corollary. The
formalization follows earlier formalizations written by Martín Escardó
{{#cite TypeTopology}} verbatim.

```agda
abstract
  has-decidable-Σ-pointed-bool-ℕ∞↗' :
    has-decidable-Σ-pointed-bool' ℕ∞↗
  has-decidable-Σ-pointed-bool-ℕ∞↗' p = (a , lemma)
    where
    a : ℕ∞↗
    a = force-ℕ∞↗ (p ∘ increasing-binary-sequence-ℕ)

    dagger₀ :
      (n : ℕ) →
      a ＝ increasing-binary-sequence-ℕ n →
      p (increasing-binary-sequence-ℕ n) ＝ true
    dagger₀ 0 r =
      ap (ev-ℕ∞↗ 0) r
    dagger₀ (succ-ℕ n) r =
      ( inv
        ( ap
          ( or-bool (p (increasing-binary-sequence-ℕ (succ-ℕ n))))
          ( ( ap (ev-ℕ∞↗ n) r) ∙
            ( is-strictly-bounded-below-increasing-binary-sequence-succ-ℕ n)) ∙
          ( right-unit-law-or-bool))) ∙
      ( ap (ev-ℕ∞↗ (succ-ℕ n)) r) ∙
      ( is-finitely-bounded-increasing-binary-sequence-ℕ n)

    dagger₁ :
      a ＝ infinity-ℕ∞↗ → (n : ℕ) → p (increasing-binary-sequence-ℕ n) ＝ false
    dagger₁ r 0 = ap (ev-ℕ∞↗ 0) r
    dagger₁ r (succ-ℕ n) =
      ( inv
        ( ( ap
            ( or-bool (p (increasing-binary-sequence-ℕ (succ-ℕ n))))
            ( ap (ev-ℕ∞↗ n) r)) ∙
          ( right-unit-law-or-bool))) ∙
      ( ap (ev-ℕ∞↗ (succ-ℕ n)) r)

    lemma₀ :
      (n : ℕ) → a ＝ increasing-binary-sequence-ℕ n → p a ＝ true
    lemma₀ n t = ap p t ∙ dagger₀ n t

    claim₀ :
      p a ＝ false → (n : ℕ) → a ≠ increasing-binary-sequence-ℕ n
    claim₀ r n s = neq-false-true-bool (inv r ∙ lemma₀ n s)

    claim₁ :
      p a ＝ false → a ＝ infinity-ℕ∞↗
    claim₁ r =
      eq-infinity-is-not-in-image-increasing-binary-sequence-ℕ a (claim₀ r)

    claim₂ :
      p a ＝ false → (n : ℕ) → p (increasing-binary-sequence-ℕ n) ＝ false
    claim₂ r = dagger₁ (claim₁ r)

    claim₃ :
      p a ＝ false → p infinity-ℕ∞↗ ＝ false
    claim₃ r = ap p (inv (claim₁ r)) ∙ r

    lemma :
      p a ＝ false → (v : ℕ∞↗) → p v ＝ false
    lemma r =
      htpy-ℕ∞↗-htpy-ℕ+∞
        ( λ _ → has-double-negation-stable-equality-bool)
        ( claim₂ r)
        ( claim₃ r)
```

## Corollaries

### The type of increasing binary sequences has decidable Σ-types

```agda
abstract
  has-decidable-Σ-pointed-bool-ℕ∞↗ :
    has-decidable-Σ-pointed-bool ℕ∞↗
  has-decidable-Σ-pointed-bool-ℕ∞↗ =
    flip-has-decidable-Σ-pointed-bool
      ( has-decidable-Σ-pointed-bool-ℕ∞↗')

has-decidable-type-subtype-pointed-ℕ∞↗ :
  has-decidable-type-subtype-pointed ℕ∞↗
has-decidable-type-subtype-pointed-ℕ∞↗ =
  has-decidable-type-subtype-pointed-has-decidable-Σ-pointed-bool
    ( has-decidable-Σ-pointed-bool-ℕ∞↗)

has-decidable-Σ-pointed-ℕ∞↗ : has-decidable-Σ-pointed ℕ∞↗
has-decidable-Σ-pointed-ℕ∞↗ =
  has-decidable-Σ-pointed-has-decidable-type-subtype-pointed
    ( has-decidable-type-subtype-pointed-ℕ∞↗)

has-decidable-Σ-ℕ∞↗ : has-decidable-Σ ℕ∞↗
has-decidable-Σ-ℕ∞↗ =
  has-decidable-Σ-has-decidable-Σ-pointed
    ( has-decidable-Σ-pointed-ℕ∞↗)
```

### The type of increasing binary sequences has decidable Π-types

```agda
has-decidable-Π-ℕ∞↗ : has-decidable-Π ℕ∞↗
has-decidable-Π-ℕ∞↗ =
  has-decidable-Π-has-decidable-Σ has-decidable-Σ-ℕ∞↗
```

## References

- [`TypeTopology.GenericConvergentSequenceCompactness`](https://martinescardo.github.io/TypeTopology/TypeTopology.GenericConvergentSequenceCompactness.html)
  at TypeTopology {{#cite TypeTopology}}

{{#bibliography}}
