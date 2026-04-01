# Reversed tuples

```agda
module lists.reversed-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types
open import foundation.universe-levels

open import lists.equality-tuples
open import lists.tuples
```

</details>

## Idea

## Definition

```agda
module _
  {l : Level}
  {A : UU l}
  where

  reverse-tuple : {n : ℕ} → tuple A n → tuple A n
  reverse-tuple empty-tuple = empty-tuple
  reverse-tuple (x ∷ v) = snoc-tuple (reverse-tuple v) x
```
