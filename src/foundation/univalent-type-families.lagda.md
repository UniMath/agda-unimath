# Univalent type families

```agda
module foundation.univalent-type-families where
```

<details><summary>Imports</summary>

```agda
open import foundation.transport
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
```

</details>

## Idea

A type family `B` over `A` is said to be univalent if the map

```text
  equiv-tr : (Id x y) → (B x ≃ B y)
```

is an equivalence for every `x y : A`.

## Definition

```agda
is-univalent :
  {l1 l2 : Level} {A : UU l1} → (A → UU l2) → UU (l1 ⊔ l2)
is-univalent {A = A} B = (x y : A) → is-equiv (λ (p : x ＝ y) → equiv-tr B p)
```
