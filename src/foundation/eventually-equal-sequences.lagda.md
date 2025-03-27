# Eventually equal sequences

```agda
module foundation.eventually-equal-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Two [sequences](foundation.sequences.md) `u` and `v` are
{{#concept "eventually equal" Agda=eventually-eq-sequence}} if `u n ＝ v n` for
any sufficiently large natural number `n`.

## Definition

### The relation of being eventually equal sequences

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  is-modulus-eventually-eq-sequence : ℕ → UU l
  is-modulus-eventually-eq-sequence N = (m : ℕ) → leq-ℕ N m → u m ＝ v m

  eventually-eq-sequence : UU l
  eventually-eq-sequence = Σ ℕ is-modulus-eventually-eq-sequence

  modulus-eventually-eq-sequence :
    eventually-eq-sequence → ℕ
  modulus-eventually-eq-sequence H = pr1 H

  eq-leq-modulus-eventually-eq-sequence :
    (H : eventually-eq-sequence) →
    is-modulus-eventually-eq-sequence
      (modulus-eventually-eq-sequence H)
  eq-leq-modulus-eventually-eq-sequence H = pr2 H
```

## Properties

### Any sequence is eventually equal to itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-eventually-eq-sequence : eventually-eq-sequence u u
  pr1 refl-eventually-eq-sequence = zero-ℕ
  pr2 refl-eventually-eq-sequence m H = refl
```

### Eventual equality is a symmetric relation

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  symmetric-eventually-eq-sequence :
    eventually-eq-sequence u v → eventually-eq-sequence v u
  symmetric-eventually-eq-sequence = tot (λ N H m K → inv (H m K))
```

### Eventual equality is a transitive relation

```agda
module _
  {l : Level} {A : UU l} (u v w : sequence A)
  where

  transitive-eventually-eq-sequence :
    eventually-eq-sequence v w →
    eventually-eq-sequence u v →
    eventually-eq-sequence u w
  transitive-eventually-eq-sequence (n , H) (m , K) =
    ( max-ℕ m n) ,
    ( λ p I →
      ( K p (leq-left-leq-max-ℕ p m n I)) ∙
      ( H p (leq-right-leq-max-ℕ p m n I)))
```
