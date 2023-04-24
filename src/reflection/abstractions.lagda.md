# Abstractions

```agda
module reflection.abstractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.strings
open import foundation.universe-levels
```

</details>

## Idea

The `Abs` type represents a lambda abstraction.

## Definition

```agda
data Abs {l} (A : UU l) : UU l where
  abs : String → A → Abs A

{-# BUILTIN ABS    Abs #-}
{-# BUILTIN ABSABS abs #-}
```
