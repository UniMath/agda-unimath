# Abstractions

```agda
module reflection.abstractions where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import primitives.strings
```

</details>

## Idea

The `Abstraction-Agda` type represents a lambda abstraction.

## Definition

```agda
data Abstraction-Agda {l} (A : UU l) : UU l where
  abs : String → A → Abstraction-Agda A

{-# BUILTIN ABS Abstraction-Agda #-}
{-# BUILTIN ABSABS abs #-}
```
