# Connected types

<details><summary>Imports</summary>
```agda
module foundation.connected-types where
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-truncation
open import foundation.propositions
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
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
  is-equiv (const A (type-Truncated-Type B))
is-equiv-diagonal-is-connected B H =
  is-equiv-comp
    ( precomp unit-trunc (type-Truncated-Type B))
    ( λ b → const _ _ b)
    ( is-equiv-diagonal-is-contr H (type-Truncated-Type B))
    ( is-truncation-trunc B)

is-connected-is-equiv-diagonal :
  {l1 : Level} {k : 𝕋} {A : UU l1} →
  ({l2 : Level} (B : Truncated-Type l2 k) → is-equiv (const A (type-Truncated-Type B))) →
  is-connected k A
is-connected-is-equiv-diagonal {k = k} {A = A} H =
  tot
    ( λ x →
      function-dependent-universal-property-trunc
        ( Id-Truncated-Type' (trunc k A) x))
    ( tot (λ _ → htpy-eq) (center (is-contr-map-is-equiv (H (trunc k A)) unit-trunc)))
```

### A contractible type is `k`-connected for any `k`

```agda
is-connected-is-contr :
  {l1 : Level} (k : 𝕋) {A : UU l1} →
  is-contr A → is-connected k A
is-connected-is-contr k H =
  is-connected-is-equiv-diagonal
    λ B → is-equiv-diagonal-is-contr H (type-Truncated-Type B)
```

### A type that is `(k+1)`-connected is `k`-connected

```agda
is-connected-is-connected-succ-𝕋 :
  {l1 : Level} (k : 𝕋) {A : UU l1} →
  is-connected (succ-𝕋 k) A → is-connected k A
is-connected-is-connected-succ-𝕋 k H =
  is-connected-is-equiv-diagonal
    λ B → is-equiv-diagonal-is-connected (truncated-type-succ-Truncated-Type k B) H
```

### Any type that is equivalent to a `k`-connected type is `k`-connected

```agda
is-connected-equiv :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2} →
  A ≃ B → is-connected k B → is-connected k A
is-connected-equiv k e H = is-contr-equiv _ (equiv-trunc k e) H
```

### The total space of a family of `k`-connected types over a `k`-connected type is `k`-connected

```agda
is-connected-Σ :
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : A → UU l2} →
  is-connected k A → ((x : A) → is-connected k (B x)) →
  is-connected k (Σ A B)
is-connected-Σ k H K =
  is-contr-equiv _ (equiv-trunc k (equiv-pr1 K) ∘e equiv-trunc-Σ k) H
```
