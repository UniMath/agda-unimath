# Unpointed maps between pointed types

```agda
module structured-types.unpointed-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

The type of {{#concept "unpointed maps" Agda=unpointed-map-Pointed-Type}}
between [pointed types](structured-types.pointed-types.md) is a pointed type,
pointed at the constant function.

## Definition

```agda
unpointed-map-Pointed-Type :
  {l1 l2 : Level} → Pointed-Type l1 → Pointed-Type l2 → Pointed-Type (l1 ⊔ l2)
pr1 (unpointed-map-Pointed-Type A B) = type-Pointed-Type A → type-Pointed-Type B
pr2 (unpointed-map-Pointed-Type A B) x = point-Pointed-Type B
```
