# Symmetric elements of involutive types

```agda
module structured-types.symmetric-elements-involutive-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.involutive-types

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

Symmetric elements of involutive types are fixed points of the involution. In
other words, the type of symmetric elements of an involutive type `A` is defined
to be

```text
  (X : 2-Element-Type lzero) → A X
```

## Definition

```agda
symmetric-element-Involutive-Type :
  {l : Level} (A : Involutive-Type l) → UU (lone ⊔ l)
symmetric-element-Involutive-Type A = (X : 2-Element-Type lzero) → A X
```
