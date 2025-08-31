# Coproducts of inhabited finite types

```agda
module univalent-combinatorics.coproducts-inhabited-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.inhabited-finite-types
```

</details>

## Idea

The [coproduct](univalent-combinatorics.coproduct-types.md) of two
[inhabited finite types](univalent-combinatorics.inhabited-finite-types.md) is
itself an inhabited finite type.

## Definition

```agda
coproduct-Inhabited-Finite-Type :
  {l1 l2 : Level} → Inhabited-Finite-Type l1 → Inhabited-Finite-Type l2 →
  Inhabited-Finite-Type (l1 ⊔ l2)
pr1 (coproduct-Inhabited-Finite-Type X Y) =
  coproduct-Finite-Type
    ( finite-type-Inhabited-Finite-Type X)
    ( finite-type-Inhabited-Finite-Type Y)
pr2 (coproduct-Inhabited-Finite-Type X Y) =
  map-is-inhabited inl (is-inhabited-type-Inhabited-Finite-Type X)
```
