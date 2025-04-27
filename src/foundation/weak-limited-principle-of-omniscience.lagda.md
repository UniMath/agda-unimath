# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.equivalences
open import foundation.limited-principle-of-omniscience
open import foundation.logical-equivalences
open import foundation.negation
open import foundation.transport-along-identifications
open import foundation.universal-quantification
open import foundation.universe-levels

open import foundation-core.decidable-propositions
open import foundation-core.propositions
open import foundation-core.sets

open import logic.complements-decidable-subtypes
```

</details>

## Statement

The {{#concept "weak limited principle of omniscience" Agda=WLPO}} (WLPO)
asserts that every [decidable subtype](foundation.decidable-subtypes.md) of the
[natural numbers](elementary-number-theory.natural-numbers.md) is
[full](foundation.full-subtypes.md) or it is [not](foundation.negation.md). In
particular, it is a restricted form of the
[law of excluded middle](foundation.law-of-excluded-middle.md).

```agda
level-prop-WLPO : (l : Level) → Prop (lsuc l)
level-prop-WLPO l =
  Π-Prop
    ( decidable-subtype l ℕ)
    ( λ P →
      is-decidable-Prop (is-full-decidable-subtype-Prop P))

level-WLPO : (l : Level) → UU (lsuc l)
level-WLPO l = type-Prop (level-prop-WLPO l)

WLPO : UUω
WLPO = {l : Level} → level-WLPO l
```

## Properties

### The limited principle of omniscience implies the weak limited principle of omniscience

```agda
abstract
  level-WLPO-level-LPO : {l : Level} → level-LPO l → level-WLPO l
  level-WLPO-level-LPO lpo P =
    elim-disjunction
      ( is-decidable-Prop (is-full-decidable-subtype-Prop P))
      ( λ (a , a∉P) → inr (λ full-P → ex-falso (a∉P (full-P a))))
      ( λ ¬¬P →
        inl
          ( λ a →
            is-double-negation-stable-decidable-subtype
              ( P)
              ( a)
              ( λ a∉P → ¬¬P (a , a∉P))))
      ( lpo (complement-decidable-subtype P))
```

### Equivalent boolean formulation

```agda
bool-prop-WLPO : Prop lzero
bool-prop-WLPO =
  ∀' (ℕ → bool) (λ f → is-decidable-Prop (∀' ℕ (λ n → is-true-Prop (f n))))

bool-WLPO : UU lzero
bool-WLPO = type-Prop bool-prop-WLPO

abstract
  WLPO-bool-WLPO : bool-WLPO → WLPO
  WLPO-bool-WLPO bool-wlpo P =
    rec-coproduct
      ( λ all-true-f →
        inl (λ n → is-in-decidable-subtype-is-true-map-bool P n (all-true-f n)))
      ( λ not-all-true-f →
        inr
          ( λ full-P →
            not-all-true-f
              ( λ n → is-true-map-bool-is-in-decidable-subtype P n (full-P n))))
      ( bool-wlpo (map-equiv (map-bool-decidable-subtype-equiv ℕ) P))

  bool-WLPO-level-WLPO : {l : Level} → level-WLPO l → bool-WLPO
  bool-WLPO-level-WLPO {l} wlpo f =
    rec-coproduct
      ( λ full-P →
        inl
          ( λ n →
            tr
              ( λ g → is-true (g n))
              ( is-section-map-inv-equiv (map-bool-decidable-subtype-equiv ℕ) f)
              ( is-true-map-bool-is-in-decidable-subtype P n (full-P n))))
      ( λ not-full-P →
        inr
          ( λ all-true-f →
            not-full-P
              ( λ n →
                is-in-decidable-subtype-is-true-map-bool
                  ( P)
                  ( n)
                  ( inv-tr
                    ( λ g → is-true (g n))
                    ( is-section-map-inv-equiv
                      ( map-bool-decidable-subtype-equiv ℕ)
                      ( f))
                    ( all-true-f n)))))
      ( wlpo P)
    where
      P : decidable-subtype l ℕ
      P = map-inv-equiv (map-bool-decidable-subtype-equiv ℕ) f

  level-WLPO-iff-bool-WLPO : (l : Level) → level-WLPO l ↔ bool-WLPO
  pr1 (level-WLPO-iff-bool-WLPO _) = bool-WLPO-level-WLPO
  pr2 (level-WLPO-iff-bool-WLPO _) bwlpo = WLPO-bool-WLPO bwlpo
```

### The weak limited principle of omniscience at any level implies it at all levels

```agda
WLPO-level-WLPO : {l : Level} → level-WLPO l → WLPO
WLPO-level-WLPO level-wlpo = WLPO-bool-WLPO (bool-WLPO-level-WLPO level-wlpo)
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [`Taboos.WLPO`](https://martinescardo.github.io/TypeTopology/Taboos.WLPO.html)
  at TypeTopology
- [weak limited principle of omniscience](https://ncatlab.org/nlab/show/weak+limited+principle+of+omniscience)
  at $n$Lab
