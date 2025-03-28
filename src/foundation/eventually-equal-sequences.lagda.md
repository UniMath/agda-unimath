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
open import foundation.eventually-pointed-sequences-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sequences
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

Two [sequences](foundation.sequences.md) `u` and `v` are
{{#concept "eventually equal" Disambiguation="sequences" Agda=has-modulus-eventually-eq-sequence}}
if `u n ＝ v n` for sufficiently large
[natural numbers](elementary-number-theory.natural-numbers.md) `n : ℕ`.

## Definitions

### The relation of being eventually equal sequences

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  has-modulus-eventually-eq-sequence : UU l
  has-modulus-eventually-eq-sequence =
    has-modulus-eventually-pointed-sequence (λ n → u n ＝ v n)
```

### Modulus of eventual equality

```agda
module _
  {l : Level} {A : UU l} {u v : sequence A}
  (H : has-modulus-eventually-eq-sequence u v)
  where

  modulus-has-modulus-eventually-eq-sequence : ℕ
  modulus-has-modulus-eventually-eq-sequence = pr1 H

  is-modulus-has-modulus-eventually-eq-sequence :
    (n : ℕ) → leq-ℕ modulus-has-modulus-eventually-eq-sequence n → u n ＝ v n
  is-modulus-has-modulus-eventually-eq-sequence = pr2 H
```

## Properties

### Any sequence is asymptotically equal to itself

```agda
module _
  {l : Level} {A : UU l} (u : sequence A)
  where

  refl-has-modulus-eventually-eq-sequence :
    has-modulus-eventually-eq-sequence u u
  pr1 refl-has-modulus-eventually-eq-sequence = zero-ℕ
  pr2 refl-has-modulus-eventually-eq-sequence m H = refl
```

### Homotopic sequences are eventually equal

```agda
  has-modulus-eventually-eq-htpy-sequence :
    {u v : sequence A} → (u ~ v) → has-modulus-eventually-eq-sequence u v
  has-modulus-eventually-eq-htpy-sequence {u} {v} I = (zero-ℕ , λ n H → I n)
```

### Eventual equality is a symmetric relation

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  symmetric-has-modulus-eventually-eq-sequence :
    has-modulus-eventually-eq-sequence u v →
    has-modulus-eventually-eq-sequence v u
  symmetric-has-modulus-eventually-eq-sequence =
    map-Π-has-modulus-eventually-pointed-sequence (λ n → inv)

module _
  {l : Level} {A : UU l} {u v : sequence A}
  where

  inv-has-modulus-eventually-eq-sequence :
    has-modulus-eventually-eq-sequence u v →
    has-modulus-eventually-eq-sequence v u
  inv-has-modulus-eventually-eq-sequence =
    symmetric-has-modulus-eventually-eq-sequence u v
```

### Eventual equality is a transitive relation

```agda
module _
  {l : Level} {A : UU l} (u v w : sequence A)
  where

  transitive-has-modulus-eventually-eq-sequence :
    has-modulus-eventually-eq-sequence v w →
    has-modulus-eventually-eq-sequence u v →
    has-modulus-eventually-eq-sequence u w
  transitive-has-modulus-eventually-eq-sequence =
    map-binary-Π-has-modulus-eventually-pointed-sequence (λ n I J → J ∙ I)
```

### Conjugation of asymptotical equality

```agda
module _
  {l : Level} {A : UU l} {u u' v v' : sequence A}
  where

  conjugate-has-modulus-eventually-eq-sequence :
    has-modulus-eventually-eq-sequence u u' →
    has-modulus-eventually-eq-sequence v v' →
    has-modulus-eventually-eq-sequence u v →
    has-modulus-eventually-eq-sequence u' v'
  conjugate-has-modulus-eventually-eq-sequence H K I =
    transitive-has-modulus-eventually-eq-sequence u' u v'
      ( transitive-has-modulus-eventually-eq-sequence u v v' K I)
      ( inv-has-modulus-eventually-eq-sequence H)

  conjugate-has-modulus-eventually-eq-sequence' :
    has-modulus-eventually-eq-sequence u u' →
    has-modulus-eventually-eq-sequence v v' →
    has-modulus-eventually-eq-sequence u' v' →
    has-modulus-eventually-eq-sequence u v
  conjugate-has-modulus-eventually-eq-sequence' H K I =
    transitive-has-modulus-eventually-eq-sequence u u' v
      ( transitive-has-modulus-eventually-eq-sequence u' v' v
        (inv-has-modulus-eventually-eq-sequence K) I)
      ( H)
```
