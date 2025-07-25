# The axiom of countable choice

```agda
module foundation.axiom-of-countable-choice where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.axiom-of-choice
open import foundation.inhabited-types
-- open import foundation.axiom-of-dependent-choice
open import foundation.universe-levels
open import set-theory.countable-sets
```

</details>

## Idea

The {{#concept "axiom of countable choice" WD="axiom of countable choice" WDID=Q1000116 Agda=ACω}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `B` indexed by the
[natural numbers](elementary-number-theory.natural-numbers.md) `ℕ`, the type of
sections of that family `(n : ℕ) → B n` is inhabited.

## Definition

```agda
level-ACω : (l : Level) → UU (lsuc l)
level-ACω l =
  (f : ℕ → Inhabited-Type l) →
  is-inhabited ((n : ℕ) → type-Inhabited-Type (f n))

ACω : UUω
ACω = {l : Level} → level-ACω l
```

## Properties

### The axiom of countable choice implies choice for all countable sets

```agda
module _
  {l : Level} (X : Set l)
  (H : is-countable X)
  where

  choice-countable-set-ACω :
    instance-choice-Set A
```

### The axiom of choice implies the axiom of countable choice

```agda
level-ACω-level-AC0 : {l : Level} → level-AC0 lzero l → level-ACω l
level-ACω-level-AC0 ac0 f =
  ac0
    ( ℕ-Set)
    ( λ n → type-Inhabited-Type (f n))
    ( λ n → is-inhabited-type-Inhabited-Type (f n))

ACω-AC0 : AC0 → ACω
ACω-AC0 ac0 = level-ACω-level-AC0 ac0
```

### The axiom of dependent choice implies the axiom of countable choice

```agda
level-ACω-level-ADC : {l : Level} → level-ADC l l → level-ACω l
level-ACω-level-ADC adc f =
  let
    A = Σ ℕ (λ n → type-Inhabited-Type (f n))
    R = ?
  in {!   !}
```
