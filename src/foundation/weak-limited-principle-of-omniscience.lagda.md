# The weak limited principle of omniscience

```agda
module foundation.weak-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.disjunction
open import foundation.negation
open import foundation.universal-quantification
open import foundation.universe-levels
open import foundation.decidable-subtypes

open import foundation-core.decidable-propositions
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Statement

The {{#concept "weak limited principle of omniscience"}} (WLPO) asserts that
every [decidable subtype](foundation.decidable-subtypes.md) of the
[natural numbers](elementary-number-theory.natural-numbers.md) is
[full](foundation.full-subtypes.md) or it is [not](foundation.negation.md).
In particular, it is a restricted form of the
[law of excluded middle](foundation.law-of-excluded-middle.md).

```agda
level-WLPO-Prop : (l : Level) → Prop (lsuc l)
level-WLPO-Prop l =
  Π-Prop
    ( decidable-subtype l ℕ)
    ( λ P →
      is-decidable-Prop (is-full-decidable-subtype-Prop P))

level-WLPO : (l : Level) → UU (lsuc l)
level-WLPO l = type-Prop (level-WLPO-Prop l)

WLPO : UUω
WLPO = {l : Level} → level-WLPO l
```

### Equivalent Boolean formulation

```agda
bool-WLPO-Prop : Prop lzero
bool-WLPO-Prop =
  ∀' (ℕ → bool) (λ f → is-decidable-Prop (∀' ℕ (λ n → is-true-Prop (f n))))

bool-WLPO : UU lzero
bool-WLPO = type-Prop bool-WLPO

abstract
  -- bool-WLPO-level-WLPO :
```

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The lesser limited principle of omniscience](foundation.lesser-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.WLPO](https://martinescardo.github.io/TypeTopology/Taboos.WLPO.html)
  at TypeTopology
- [weak limited principle of omniscience](https://ncatlab.org/nlab/show/weak+limited+principle+of+omniscience)
  at $n$Lab
