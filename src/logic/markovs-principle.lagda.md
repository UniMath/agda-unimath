# Markov's principle

```agda
module logic.markovs-principle where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

{{#concept "Markov's principle" WDID=Q3922074 WD="Markov's principle" Agda=Markov's-Principle}}
asserts that if a [decidable subtype](foundation.decidable-subtypes.md) `𝒫` of
the [natural numbers](elementary-number-theory.natural-numbers.md) `ℕ` is not
[full](foundation.full-subtypes.md), then
[there is](foundation.existential-quantification.md) a natural number `n` that
is not in `𝒫`.

More generally we say a type `A` is {{#concept "Markovian" Agda=is-markovian}}
if, for every decidable subtype `𝒫` of `A`, if `𝒫` is not full then there is an
element of `A` that is not in `𝒫`.

Markov's principle is an example of a constructive taboo. That is, it is an
example of a principle that need not be true in constructive mathematics,
although, it does not imply the
[law of excluded middle](foundation.law-of-excluded-middle.md).

## Definitions

### The predicate on a type of being Markovian

We phrase the condition using booleans to obtain a small predicate.

```agda
is-markovian : {l : Level} → UU l → UU l
is-markovian A =
  (𝒫 : (x : A) → bool) →
  ¬ ((x : A) → is-true (𝒫 x)) →
  is-inhabited (Σ A (is-false ∘ 𝒫))

is-prop-is-markovian : {l : Level} (A : UU l) → is-prop (is-markovian A)
is-prop-is-markovian A =
  is-prop-Π
    ( λ 𝒫 →
      is-prop-function-type
        ( is-property-is-inhabited (Σ A (is-false ∘ 𝒫))))
```

### The predicate on a type of being Markovian at a universe level

```agda
module _
  {l1 : Level} (l2 : Level) (A : UU l1)
  where

  is-markovian-prop-Level : Prop (l1 ⊔ lsuc l2)
  is-markovian-prop-Level =
    Π-Prop
      ( decidable-subtype l2 A)
      ( λ P →
        ¬' (∀' A (subtype-decidable-subtype P)) ⇒
        ∃ A (¬'_ ∘ subtype-decidable-subtype P))

  is-markovian-Level : UU (l1 ⊔ lsuc l2)
  is-markovian-Level =
      (P : decidable-subtype l2 A) →
      ¬ ((x : A) → is-in-decidable-subtype P x) →
      exists A (¬'_ ∘ subtype-decidable-subtype P)

  is-prop-is-markovian-Level : is-prop is-markovian-Level
  is-prop-is-markovian-Level = is-prop-type-Prop is-markovian-prop-Level
```

### Markov's principle

```agda
Markov's-Principle : UU lzero
Markov's-Principle = is-markovian ℕ
```

## Properties

### A type is Markovian if and only if it is Markovian at all universe levels

> This remains to be formalized.

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)

## External links

- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
