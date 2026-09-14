# Conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module elementary-number-theory.conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.homotopies
open import foundation.injective-maps
open import foundation.negated-equality
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.maybe
```

</details>

## Idea

The {{#concept "conatural numbers" Agda=ℕ∞}} `ℕ∞` is a
[set](foundation-core.sets.md) that satisfies the dual of the universal property
of [natural numbers](elementary-number-theory.natural-numbers.md) in the sense
that it is the final coalgebra of the functor `X ↦ 1 + X` rather than the
initial algebra.

## Definitions

### The coinductive type of conatural numbers

```agda
record ℕ∞ : UU lzero
  where
  coinductive
  constructor cons-ℕ∞
  field
    decons-ℕ∞ : Maybe ℕ∞

open ℕ∞ public
```

### The zero element of the conatural numbers

```agda
zero-ℕ∞ : ℕ∞
decons-ℕ∞ zero-ℕ∞ = exception-Maybe
```

### The element at infinity of the conatural numbers

```agda
infinity-ℕ∞ : ℕ∞
decons-ℕ∞ infinity-ℕ∞ = unit-Maybe infinity-ℕ∞
```

### The successor function on the conatural numbers

```agda
succ-ℕ∞ : ℕ∞ → ℕ∞
decons-ℕ∞ (succ-ℕ∞ x) = unit-Maybe x
```

### Alternative definition of the constructor function for conatural numbers

```agda
cons-ℕ∞' : Maybe ℕ∞ → ℕ∞
cons-ℕ∞' = rec-coproduct succ-ℕ∞ (λ _ → zero-ℕ∞)
```

### Alternative definition of the deconstructor function for conatural numbers

```agda
decons-ℕ∞' : ℕ∞ → Maybe ℕ∞
decons-ℕ∞' x = rec-coproduct inl inr (decons-ℕ∞ x)

compute-decons-ℕ∞ : decons-ℕ∞' ~ decons-ℕ∞
compute-decons-ℕ∞ x with decons-ℕ∞ x
compute-decons-ℕ∞ x | inl q = refl
compute-decons-ℕ∞ x | inr q = refl
```

### The coiterator function for conatural numbers

```agda
coit-ℕ∞ : {l : Level} {A : UU l} → (A → Maybe A) → A → ℕ∞
decons-ℕ∞ (coit-ℕ∞ f x) with f x
decons-ℕ∞ (coit-ℕ∞ f x) | inl a = unit-Maybe (coit-ℕ∞ f a)
decons-ℕ∞ (coit-ℕ∞ f x) | inr _ = exception-Maybe

compute-decons-coit-ℕ∞ :
  {l : Level} {A : UU l} (f : A → Maybe A) (x : A) →
  decons-ℕ∞ (coit-ℕ∞ f x) ＝ map-Maybe (coit-ℕ∞ f) (f x)
compute-decons-coit-ℕ∞ f x with f x
... | inl y = refl
... | inr y = refl
```

### The corecursor function for conatural numbers

```agda
corec-ℕ∞ : {l : Level} {A : UU l} → (A → ℕ∞ + Maybe A) → A → ℕ∞
decons-ℕ∞ (corec-ℕ∞ f x) with f x
decons-ℕ∞ (corec-ℕ∞ f x) | inl q = unit-Maybe q
decons-ℕ∞ (corec-ℕ∞ f x) | inr (inl a) = unit-Maybe (corec-ℕ∞ f a)
decons-ℕ∞ (corec-ℕ∞ f x) | inr (inr *) = inr *
```

## Properties

### Zero is not a successor

```agda
neq-zero-succ-ℕ∞ : (x : ℕ∞) → succ-ℕ∞ x ≠ zero-ℕ∞
neq-zero-succ-ℕ∞ x p = is-not-exception-unit-Maybe x (ap decons-ℕ∞ p)
```

### Zero is not the point at infinity

```agda
neq-zero-infinity-ℕ∞ : infinity-ℕ∞ ≠ zero-ℕ∞
neq-zero-infinity-ℕ∞ p =
  is-not-exception-unit-Maybe infinity-ℕ∞ (ap decons-ℕ∞ p)

neq-infinity-zero-ℕ∞ : zero-ℕ∞ ≠ infinity-ℕ∞
neq-infinity-zero-ℕ∞ =
  is-symmetric-nonequal infinity-ℕ∞ zero-ℕ∞ neq-zero-infinity-ℕ∞
```

### The constructor function is a section of the deconstructor

```agda
is-section-cons-ℕ∞ : is-section decons-ℕ∞ cons-ℕ∞
is-section-cons-ℕ∞ (inl x) = refl
is-section-cons-ℕ∞ (inr x) = refl

section-decons-ℕ∞ : section decons-ℕ∞
section-decons-ℕ∞ = cons-ℕ∞ , is-section-cons-ℕ∞

retraction-cons-ℕ∞ : retraction cons-ℕ∞
retraction-cons-ℕ∞ = decons-ℕ∞ , is-section-cons-ℕ∞

is-injective-cons-ℕ∞ : is-injective cons-ℕ∞
is-injective-cons-ℕ∞ = is-injective-retraction cons-ℕ∞ retraction-cons-ℕ∞
```

```agda
is-section-cons-ℕ∞' : is-section decons-ℕ∞' cons-ℕ∞
is-section-cons-ℕ∞' (inl x) = refl
is-section-cons-ℕ∞' (inr x) = refl

section-decons-ℕ∞' : section decons-ℕ∞'
section-decons-ℕ∞' = cons-ℕ∞ , is-section-cons-ℕ∞'

retraction-cons-ℕ∞' : retraction cons-ℕ∞
retraction-cons-ℕ∞' = decons-ℕ∞' , is-section-cons-ℕ∞'

is-section-cons-ℕ∞'' : is-section decons-ℕ∞' cons-ℕ∞'
is-section-cons-ℕ∞'' (inl x) = refl
is-section-cons-ℕ∞'' (inr x) = refl

is-injective-cons-ℕ∞' : is-injective cons-ℕ∞'
is-injective-cons-ℕ∞' =
  is-injective-retraction cons-ℕ∞' (decons-ℕ∞' , is-section-cons-ℕ∞'')
```

### The successor function is injective

```agda
is-injective-succ-ℕ∞ : is-injective succ-ℕ∞
is-injective-succ-ℕ∞ p = is-injective-inl (is-injective-cons-ℕ∞' p)
```

## External links

- [CoNaturals](https://martinescardo.github.io/TypeTopology/CoNaturals.index.html)
  at TypeTopology
- [extended natural numbers](https://ncatlab.org/nlab/show/extended+natural+number)
  at $n$Lab
