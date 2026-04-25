# Constant grids

```agda
module linear-algebra.constant-grids where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.constant-tuples
open import linear-algebra.grids
```

</details>

## Idea

Constant grids are [grids](linear-algebra.grids.md) in which all elements are
the same.

## Definition

```agda
constant-grid : {l : Level} {A : UU l} {m n : ℕ} → A → grid A m n
constant-grid a = constant-tuple (constant-tuple a)
```
