# Central H-spaces

```agda
module structured-types.central-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

In [`structured-types.coherent-h-spaces`](structured-types.coherent-h-spaces.md) we saw that the type of coherent H-space structures on a pointed type `A` is equivalently described as the type of pointed sections of the pointed evaluation map `(A → A) →* A`. If the type `A` is connected, then the section maps to the connected component of `(A ≃ A)` at the identity equivalence. An evaluative H-space is a pointed type such that the map `ev_pt : (A ≃ A)_{(id)} → A` is an equivalence.

## Definition

```agda
is-central-h-space :
  {l : Level} (A : Pointed-Type l) → UU l
is-central-h-space A =
  is-equiv {A = type-Pointed-Type A → type-Pointed-Type A} (ev-pt-Pointed-Type A)
```
