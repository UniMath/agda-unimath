# Sorial type families

```agda
module foundation.sorial-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.equivalences

open import structured-types.pointed-types
```

</details>

## Idea

The notion of _sorial type family_ is a generalization of the notion of
[torsorial type family](foundation.torsorial-type-families.md). Recall that if a
type family `E` over a [pointed type](structured-types.pointed-types.md) `B` is
torsorial, then we obtain in a canonical way, for each `x : B` an action

```text
  E x → (E pt ≃ E x)
```

A **sorial type family** is a type family `E` over a pointed type `B` for which
we have such an action.

## Definitions

### Sorial type families

```agda
module _
  {l1 l2 : Level} (B : Pointed-Type l1) (E : type-Pointed-Type B → UU l2)
  where

  is-sorial-family-of-types : UU (l1 ⊔ l2)
  is-sorial-family-of-types =
    (x : type-Pointed-Type B) → E x → (E (point-Pointed-Type B) ≃ E x)
```
