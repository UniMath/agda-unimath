# Asymptotically equal sequences

```agda
module foundation.asymptotically-equal-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.maximum-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.asymptotical-dependent-sequences
open import foundation.dependent-pair-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Two sequences `u` and `v` are **asymptotically equal** if `u n ＝ v n` for any
sufficiently large natural number `n`.

## Definition

### The relation of being asymptotically equal sequences

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  eq-∞-sequence : UU l
  eq-∞-sequence = asymptotically (λ n → u n ＝ v n)
```

```agda
module _
  {l : Level} {A : UU l} {u v : sequence A} (H : eq-∞-sequence u v)
  where

  modulus-eq-∞-sequence : ℕ
  modulus-eq-∞-sequence = pr1 H

  is-modulus-eq-∞-sequence :
    (n : ℕ) → leq-ℕ modulus-eq-∞-sequence n → u n ＝ v n
  is-modulus-eq-∞-sequence = pr2 H
```

## Properties

### Any sequence is asymptotically equal to itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-eq-∞-sequence : eq-∞-sequence u u
  pr1 refl-eq-∞-sequence = zero-ℕ
  pr2 refl-eq-∞-sequence m H = refl
```

### Asymptotical equality is a symmetric relation

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  symmetric-eq-∞-sequence : eq-∞-sequence u v → eq-∞-sequence v u
  symmetric-eq-∞-sequence =
    map-Σ
      ( is-modulus-dependent-sequence (λ n → v n ＝ u n))
      ( id)
      ( λ N H m K → inv (H m K))
```

### Asymptotical equality is a transitive relation

```agda
module _
  {l : Level} {A : UU l} (u v w : sequence A)
  where

  transitive-eq-∞-sequence :
    eq-∞-sequence v w →
    eq-∞-sequence u v →
    eq-∞-sequence u w
  transitive-eq-∞-sequence (n , H) (m , K) =
    ( max-ℕ m n) ,
    ( λ p I →
      ( K p (leq-left-leq-max-ℕ p m n I)) ∙
      ( H p (leq-right-leq-max-ℕ p m n I)))
```
