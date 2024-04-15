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
data Abstraction-Agda {l : Level} (A : UU l) : UU l where
  cons-Abstraction-Agda : String → A → Abstraction-Agda A

{-# BUILTIN ABS Abstraction-Agda #-}
{-# BUILTIN ABSABS cons-Abstraction-Agda #-}
```
