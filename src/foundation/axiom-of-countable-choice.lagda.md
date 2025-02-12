# The axiom of countable choice

```agda
module foundation.axiom-of-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.axiom-of-weak-countable-choice
open import foundation.function-types
open import foundation.inhabited-types
open import foundation.sets
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "axiom of countable choice" WD="axiom of countable choice" WDID=Q1000116 Agda=ACω}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `F` indexed by the type `ℕ` of [natural numbers](elementary-number-theory.natural-numbers.md), the
type of sections of that family `(n : ℕ) → B n` is inhabited.

## Definition

### Instances of choice

```agda
instance-countable-choice : {l : Level} → (ℕ → UU l) → UU l
instance-countable-choice F =
  ((n : ℕ) → is-inhabited (F n)) → is-inhabited ((n : ℕ) → F n)
```

### The axiom of countable choice

```agda
instance-countable-choice-Set :
  {l : Level} → (ℕ → Set l) → UU l
instance-countable-choice-Set F =
  instance-countable-choice (type-Set ∘ F)

level-ACω : (l : Level) → UU (lsuc l)
level-ACω l = (F : ℕ → Set l) → instance-countable-choice-Set F

ACω : UUω
ACω = {l : Level} → level-ACω l
```

## Properties

### The axiom of countable choice implies the axiom of weak countable choice

```agda
instance-weak-countable-choice-instance-countable-choice :
  {l : Level} → (F : ℕ → UU l) →
  instance-countable-choice F → instance-weak-countable-choice F
instance-weak-countable-choice-instance-countable-choice F cc inhab-F _ =
  cc inhab-F

instance-weak-countable-choice-instance-countable-choice-Set :
  {l : Level} → (F : ℕ → Set l) →
  instance-countable-choice-Set F → instance-weak-countable-choice-Set F
instance-weak-countable-choice-instance-countable-choice-Set F =
  instance-weak-countable-choice-instance-countable-choice (type-Set ∘ F)

level-WCC-level-ACω : {l : Level} → level-ACω l → level-WCC l
level-WCC-level-ACω acω-l F =
  instance-weak-countable-choice-instance-countable-choice-Set F (acω-l F)

WCC-ACω : ACω → WCC
WCC-ACω acω = level-WCC-level-ACω acω
```

## External links

- [Axiom of countable choice](https://ncatlab.org/nlab/show/countable+choice) at
  nLab
