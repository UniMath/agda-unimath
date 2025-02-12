# The axiom of weak countable choice

```agda
module foundation.axiom-of-weak-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.contractible-types
open import foundation.disjunction
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "axiom of weak countable choice" Agda=WCC}} asserts that for
every family of [inhabited](foundation.inhabited-types.md) types `F` indexed by
[`ℕ`](elementary-number-theory.natural-numbers.md), where for at most one `n`,
`F n` is [contractible](foundation.contractible-types.md), the type of sections
of that family `(n : ℕ) → B n` is inhabited.

## Definitions

### Instances of weak countable choice

```agda
instance-weak-countable-choice : {l : Level} → (ℕ → UU l) → UU l
instance-weak-countable-choice F =
  ( (n : ℕ) → is-inhabited (F n)) →
  ( (m n : ℕ) →
    le-ℕ m n →
    type-Prop (is-contr-Prop (F m) ∨ is-contr-Prop (F n))) →
  is-inhabited ((n : ℕ) → F n)
```

### The axiom of weak countable choice

```agda
instance-weak-countable-choice-Set :
  {l : Level} → (ℕ → Set l) → UU l
instance-weak-countable-choice-Set F =
  instance-weak-countable-choice (type-Set ∘ F)

level-WCC : (l : Level) → UU (lsuc l)
level-WCC l = (F : ℕ → Set l) → instance-weak-countable-choice-Set F

WCC : UUω
WCC = {l : Level} → level-WCC l
```

## External links

- [Weak countable choice](https://ncatlab.org/nlab/show/countable+choice#WCC) at
  nLab
