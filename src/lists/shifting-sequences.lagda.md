# Shifting sequences

```agda
module lists.shifting-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels
```

</details>

## Idea

Given a sequence `f : ℕ → A` and an element `a : A` we define
`shift-ℕ a f : ℕ → A` by

```text
  shift-ℕ a f zero-ℕ := a
  shift-ℕ a f (succ-ℕ n) := f n
```

## Definition

```agda
shift-ℕ : {l : Level} {A : UU l} (a : A) (f : ℕ → A) → ℕ → A
shift-ℕ a f zero-ℕ = a
shift-ℕ a f (succ-ℕ n) = f n
```
