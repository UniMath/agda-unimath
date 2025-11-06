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

Given a [sequence](lists.sequences.md) `f : ℕ → A` and an element `a : A` we
define a
{{#concept "right shift operation" Disambiguation="on sequences" Agda=shift-ℕ}}
`shift-ℕ a f : ℕ → A` by

```text
  shift-ℕ a f zero-ℕ := a
  shift-ℕ a f (succ-ℕ n) := f n.
```

We think of this operation as moving every element to the right, and padding
with the value `a`.

## Definition

```agda
shift-ℕ : {l : Level} {A : UU l} (a : A) (f : ℕ → A) → ℕ → A
shift-ℕ a f zero-ℕ = a
shift-ℕ a f (succ-ℕ n) = f n
```
