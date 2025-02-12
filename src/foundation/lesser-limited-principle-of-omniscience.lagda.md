# The lesser limited principle of omniscience

```agda
module foundation.lesser-limited-principle-of-omniscience where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.parity-natural-numbers

open import foundation.contractible-types
open import foundation.decidable-subtypes
open import foundation.disjunction
open import foundation.function-types
open import foundation.negation
open import foundation.propositions
open import foundation.universal-quantification
open import foundation.universe-levels
open import foundation.weak-limited-principle-of-omniscience
```

</details>

## Statement

The {{#concept "lesser limited principle of omniscience" Agda=LLPO}} (LLPO)
asserts that any [contractible](foundation.contractible-types.md)
[decidable subtype](foundation.decidable-subtypes.md) of the
[natural numbers](elementary-number-theory.natural-numbers.md) either contains
no even numbers or contains no odd numbers.

### Instances of LLPO

```agda
instance-LLPO-Prop :
  {l : Level} →
  (S : decidable-subtype l ℕ) →
  is-contr (type-decidable-subtype S) →
  Prop l
instance-LLPO-Prop S H =
  (∀'
    ( ℕ)
    ( λ n → function-Prop (is-even-ℕ n) (¬' (subtype-decidable-subtype S n)))) ∨
  (∀'
    ( ℕ)
    ( λ n → function-Prop (is-odd-ℕ n) (¬' (subtype-decidable-subtype S n))))

instance-LLPO :
  {l : Level} →
  (S : decidable-subtype l ℕ) →
  is-contr (type-decidable-subtype S) →
  UU l
instance-LLPO S H = type-Prop (instance-LLPO-Prop S H)
```

### The lesser limited principle of omniscience

```agda
level-LLPO : (l : Level) → UU (lsuc l)
level-LLPO l =
  (S : decidable-subtype l ℕ) →
  (H : is-contr (type-decidable-subtype S)) →
  instance-LLPO S H

LLPO : UUω
LLPO = {l : Level} → level-LLPO l
```

## Properties

### The weak limited principle of omniscience implies the lesser limited principle of omniscience

TODO

## See also

- [The principle of omniscience](foundation.principle-of-omniscience.md)
- [The limited principle of omniscience](foundation.limited-principle-of-omniscience.md)
- [The weak limited principle of omniscience](foundation.weak-limited-principle-of-omniscience.md)
- [Markov's principle](logic.markovs-principle.md)

## External links

- [Taboos.LLPO](https://martinescardo.github.io/TypeTopology/Taboos.LLPO.html)
  at TypeTopology
- [lesser limited principle of omniscience](https://ncatlab.org/nlab/show/lesser+limited+principle+of+omniscience)
  at $n$Lab
