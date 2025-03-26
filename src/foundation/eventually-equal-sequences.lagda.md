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
{{#concept "eventually equal" Disambiguation="sequences" Agda=eventually-eq-sequence}}
if `u n ＝ v n` for sufficiently large
[natural numbers](elementary-number-theory.natural-numbers.md) `n : ℕ`.

## Definitions

### The relation of being eventually equal sequences

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  eventually-eq-sequence : UU l
  eventually-eq-sequence = is-eventually-pointed-sequence (λ n → u n ＝ v n)
```

### Modulus of eventual equality

```agda
module _
  {l : Level} {A : UU l} {u v : sequence A} (H : eventually-eq-sequence u v)
  where

  modulus-eventually-eq-sequence : ℕ
  modulus-eventually-eq-sequence = pr1 H

  is-modulus-eventually-eq-sequence :
    (n : ℕ) → leq-ℕ modulus-eventually-eq-sequence n → u n ＝ v n
  is-modulus-eventually-eq-sequence = pr2 H
```

## Properties

### Any sequence is asymptotically equal to itself

```agda
module _
  {l : Level} {A : UU l}
  where

  refl-eventually-eq-sequence : (u : sequence A) → eventually-eq-sequence u u
  pr1 (refl-eventually-eq-sequence u) = zero-ℕ
  pr2 (refl-eventually-eq-sequence u) m H = refl
```

### Homotopic sequences are eventually equal

```agda
  eventually-eq-htpy-sequence :
    {u v : sequence A} → (u ~ v) → eventually-eq-sequence u v
  eventually-eq-htpy-sequence {u} {v} I = (zero-ℕ , λ n H → I n)
```

### Eventual equality is a symmetric relation

```agda
module _
  {l : Level} {A : UU l} (u v : sequence A)
  where

  symmetric-eventually-eq-sequence :
    eventually-eq-sequence u v → eventually-eq-sequence v u
  symmetric-eventually-eq-sequence =
    map-Π-is-eventually-pointed-sequence (λ n → inv)

module _
  {l : Level} {A : UU l} {u v : sequence A}
  where

  inv-eventually-eq-sequence :
    eventually-eq-sequence u v → eventually-eq-sequence v u
  inv-eventually-eq-sequence = symmetric-eventually-eq-sequence u v
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
  transitive-eventually-eq-sequence =
    map-binary-Π-is-eventually-pointed-sequence (λ n I J → J ∙ I)
```

### Conjugation of asymptotical equality

```agda
module _
  {l : Level} {A : UU l} {u u' v v' : sequence A}
  where

  conjugate-eventually-eq-sequence :
    eventually-eq-sequence u u' →
    eventually-eq-sequence v v' →
    eventually-eq-sequence u v →
    eventually-eq-sequence u' v'
  conjugate-eventually-eq-sequence H K I =
    transitive-eventually-eq-sequence u' u v'
      ( transitive-eventually-eq-sequence u v v' K I)
      ( inv-eventually-eq-sequence H)

  conjugate-eventually-eq-sequence' :
    eventually-eq-sequence u u' →
    eventually-eq-sequence v v' →
    eventually-eq-sequence u' v' →
    eventually-eq-sequence u v
  conjugate-eventually-eq-sequence' H K I =
    transitive-eventually-eq-sequence u u' v
      ( transitive-eventually-eq-sequence u' v' v
        (inv-eventually-eq-sequence K) I)
      ( H)
```
