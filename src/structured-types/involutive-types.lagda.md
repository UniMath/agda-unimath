# Involutive types

```agda
module structured-types.involutive-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.universe-levels

open import univalent-combinatorics.2-element-types
```

</details>

## Idea

{{#concept "Involutive types" Agda=Involutive-Type}} are types equipped with a
`ℤ/2`-action. In other words, involutive types are type families over
`2-Element-Type lzero`.

Similarly, an involutive structure on a type `X` consists of a type family `Y`
over `2-Element-Type lzero` equipped with an
[equivalence](foundation-core.equivalences.md) `X ≃ Y (Fin 2)`.

## Definitions

### Involutive types

```agda
Involutive-Type : (l : Level) → UU (lsuc l)
Involutive-Type l = 2-Element-Type lzero → UU l

module _
  {l : Level} (X : Involutive-Type l)
  where

  type-Involutive-Type : UU l
  type-Involutive-Type = X (standard-2-Element-Type lzero)
```

### Involutive structure on a type

```agda
involutive-structure :
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
involutive-structure l2 X =
  Σ (Involutive-Type l2) (λ Y → X ≃ type-Involutive-Type Y)
```
