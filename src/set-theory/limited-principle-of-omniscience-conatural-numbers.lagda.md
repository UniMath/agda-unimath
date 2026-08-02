# The limited principle of omniscience and the conatural numbers

```agda
{-# OPTIONS --guardedness #-}

module set-theory.limited-principle-of-omniscience-conatural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.conatural-numbers
open import elementary-number-theory.inclusion-natural-numbers-conatural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.decidable-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.limited-principle-of-omniscience
open import foundation.maybe
open import foundation.surjective-maps

open import logic.double-negation-dense-maps
open import logic.double-negation-eliminating-maps

open import set-theory.equivalence-conatural-numbers-increasing-binary-sequences
open import set-theory.inclusion-natural-numbers-increasing-binary-sequences
open import set-theory.increasing-binary-sequences
open import set-theory.limited-principle-of-omniscience-increasing-binary-sequences
```

</details>

## Idea

We record relations between conditions on the
[conatural numbers](elementary-number-theory.conatural-numbers.md) and the
[limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
(LPO).

## Properties

### If the canonical extended inclusion into the conatural numbers is an equivalence, then LPO holds

```agda
LPO-is-surjective-conatural-number-ℕ+∞ :
  is-surjective conatural-number-ℕ+∞ → LPO
LPO-is-surjective-conatural-number-ℕ+∞ s =
  LPO-is-surjective-increasing-binary-sequence-ℕ+∞
    ( is-surjective-htpy'
      ( λ x →
        is-retraction-increasing-binary-sequence-ℕ∞
          ( increasing-binary-sequence-ℕ+∞ x))
      ( is-surjective-left-comp-equiv
        equiv-increasing-binary-sequence-ℕ∞
        ( is-surjective-htpy htpy-conatural-number-ℕ+∞ s)))

LPO-is-equiv-conatural-number-ℕ+∞ :
  is-equiv conatural-number-ℕ+∞ → LPO
LPO-is-equiv-conatural-number-ℕ+∞ e =
  LPO-is-surjective-conatural-number-ℕ+∞
    ( is-surjective-is-equiv e)
```

Since this inclusion is already a double negation dense embedding, we conclude
it suffices to assume that it is double negation eliminating.

```agda
LPO-is-double-negation-eliminating-map-conatural-number-ℕ+∞ :
  is-double-negation-eliminating-map conatural-number-ℕ+∞ → LPO
LPO-is-double-negation-eliminating-map-conatural-number-ℕ+∞ e =
  LPO-is-equiv-conatural-number-ℕ+∞
    ( is-equiv-is-double-negation-stable-emb-is-double-negation-dense-map
      ( is-double-negation-dense-conatural-number-ℕ+∞)
      ( is-emb-conatural-number-ℕ+∞ , e))

LPO-is-decidable-map-conatural-number-ℕ+∞ :
  is-decidable-map conatural-number-ℕ+∞ → LPO
LPO-is-decidable-map-conatural-number-ℕ+∞ e =
  LPO-is-double-negation-eliminating-map-conatural-number-ℕ+∞
    ( is-double-negation-eliminating-map-is-decidable-map e)
```

### If LPO holds then the canonical extended inclusion into the conatural numbers is an equivalence

```agda
is-equiv-conatural-number-ℕ+∞-LPO :
  LPO → is-equiv conatural-number-ℕ+∞
is-equiv-conatural-number-ℕ+∞-LPO lpo =
  is-equiv-left-map-triangle
    ( conatural-number-ℕ+∞)
    ( conatural-number-ℕ∞↗)
    ( increasing-binary-sequence-ℕ+∞)
    ( inv-htpy htpy-conatural-number-ℕ+∞)
    ( is-equiv-increasing-binary-sequence-ℕ+∞-LPO lpo)
    ( is-equiv-conatural-number-ℕ∞↗)
```

## See also

- [The limited principle of omniscience and increasing binary sequences](set-theory.limited-principle-of-omniscience-increasing-binary-sequences.md)
- [The weak limited principle of omniscience and the conatural numbers](set-theory.weak-limited-principle-of-omniscience-conatural-numbers.md)
