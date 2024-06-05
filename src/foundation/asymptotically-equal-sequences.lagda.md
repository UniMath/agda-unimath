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

## Definitions

### The relation of being asymptotically equal sequences

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  eq-∞-sequence : UU l
  eq-∞-sequence = asymptotically (λ n → u n ＝ v n)
```

### Modulus of asymptotical equality

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
  {l : Level} {A : UU l}
  where

  refl-eq-∞-sequence : (u : sequence A) → eq-∞-sequence u u
  pr1 (refl-eq-∞-sequence u) = zero-ℕ
  pr2 (refl-eq-∞-sequence u) m H = refl

  eq-∞-eq-sequence :
    {u v : sequence A} → ((n : ℕ) → u n ＝ v n) → eq-∞-sequence u v
  eq-∞-eq-sequence {u} {v} I = (zero-ℕ , λ n H → I n)
```

### Asymptotical equality is a symmetric relation

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  symmetric-eq-∞-sequence : eq-∞-sequence u v → eq-∞-sequence v u
  symmetric-eq-∞-sequence = map-asymptotically-Π (λ n → inv)

module _
  {l : Level} {A : UU l} {u v : sequence A}
  where

  inv-eq-∞-sequence : eq-∞-sequence u v → eq-∞-sequence v u
  inv-eq-∞-sequence = symmetric-eq-∞-sequence u v
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
  transitive-eq-∞-sequence = map-binary-asymptotically-Π (λ n I J → J ∙ I)
```

### Conjugation of asymptotical equality

```agda
module _
  {l : Level} {A : UU l} {u u' v v' : sequence A}
  where

  conjugate-eq-∞-sequence :
    eq-∞-sequence u u' →
    eq-∞-sequence v v' →
    eq-∞-sequence u v →
    eq-∞-sequence u' v'
  conjugate-eq-∞-sequence H K I =
    transitive-eq-∞-sequence u' u v'
      ( transitive-eq-∞-sequence u v v' K I)
      ( inv-eq-∞-sequence H)

  conjugate-eq-∞-sequence' :
    eq-∞-sequence u u' →
    eq-∞-sequence v v' →
    eq-∞-sequence u' v' →
    eq-∞-sequence u v
  conjugate-eq-∞-sequence' H K I =
    transitive-eq-∞-sequence u u' v
      ( transitive-eq-∞-sequence u' v' v (inv-eq-∞-sequence K) I)
      ( H)
```
