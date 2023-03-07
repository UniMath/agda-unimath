# Connected types

```agda
module foundation.connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.equivalences
open import foundation.functions
open import foundation.propositions
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels
```

</details>

## Idea

A type is said to be **`k`-connected** if its `k`-truncation is contractible.

## Definition

```agda
is-connected-Prop : {l : Level} (k : 𝕋) → UU l → Prop l
is-connected-Prop k A = is-contr-Prop (type-trunc k A)

is-connected : {l : Level} (k : 𝕋) → UU l → UU l
is-connected k A = type-Prop (is-connected-Prop k A)

is-prop-is-connected :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-connected k A)
is-prop-is-connected k A = is-prop-type-Prop (is-connected-Prop k A)
```

## Properties

### A type `A` is `k`-connected if and only if the map `B → (A → B)` is an equivalence for every `k`-truncated type `B`

```agda
is-equiv-diagonal-is-connected :
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} (B : Truncated-Type l2 k) →
  is-connected k A →
  is-equiv (λ (b : type-Truncated-Type B) → const A (type-Truncated-Type B) b)
is-equiv-diagonal-is-connected B H =
  is-equiv-comp
    ( precomp unit-trunc (type-Truncated-Type B))
    ( λ b → const _ _ b)
    ( is-equiv-diagonal-is-contr H (type-Truncated-Type B))
    ( is-truncation-trunc B)
```
