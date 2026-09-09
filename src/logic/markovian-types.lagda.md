# Markovian types

```agda
module logic.markovian-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A type `A` is {{#concept "Markovian" Disambiguation="type" Agda=is-markovian}}
if, for every [decidable subtype](foundation.decidable-subtypes.md) `𝒫` of `A`,
if `𝒫` is [not](foundation-core.negation.md) [full](foundation.full-subtypes.md)
then there is an element of `A` that is
[not in](foundation.complements-subtypes.md) `𝒫`.

## Definitions

### The predicate of being Markovian

We phrase the condition using the
[type of booleans](foundation-core.booleans.md) so that the predicate is small.

```agda
is-markovian : {l : Level} → UU l → UU l
is-markovian A =
  (𝒫 : A → bool) →
  ¬ ((x : A) → is-true (𝒫 x)) →
  exists A (λ x → is-false-Prop (𝒫 x))

is-prop-is-markovian : {l : Level} (A : UU l) → is-prop (is-markovian A)
is-prop-is-markovian A =
  is-prop-Π (λ 𝒫 → is-prop-function-type (is-prop-exists A (is-false-Prop ∘ 𝒫)))
```

### The predicate of being Markovian at a universe level

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

## Properties

### A type is Markovian if and only if it is Markovian at any universe level

> This remains to be formalized.

### A type is Markovian if and only if it is Markovian at all universe levels

> This remains to be formalized.

### Types with decidability search are Markovian

> This remains to be formalized.

## See also

- [Markov's principle](logic.markovs-principle.md)

## External links

- [limited principle of omniscience](https://ncatlab.org/nlab/show/limited+principle+of+omniscience)
  at $n$Lab
