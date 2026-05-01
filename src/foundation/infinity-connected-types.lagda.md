# ∞-connected types

```agda
module foundation.infinity-connected-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.equivalences-contractible-types
open import foundation.functoriality-truncation
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

A type is said to be
{{#concept "∞-connected" Disambiguation="type" Agda=is-∞-connected}} if it is
`k`-[connected](foundation.connected-types.md) for all
[truncation levels](foundation-core.truncation-levels.md) `k `.

## Definition

### ∞-connected types

```agda
is-∞-connected-Prop : {l : Level} (X : UU l) → Prop l
is-∞-connected-Prop X = Π-Prop 𝕋 (λ k → is-connected-Prop k X)

is-∞-connected : {l : Level} (X : UU l) → UU l
is-∞-connected X = type-Prop (is-∞-connected-Prop X)

is-prop-is-∞-connected : {l : Level} (X : UU l) → is-prop (is-∞-connected X)
is-prop-is-∞-connected X = is-prop-type-Prop (is-∞-connected-Prop X)
```

### Contractible types are ∞-connected

```agda
is-∞-connected-is-contr : {l : Level} (X : UU l) → is-contr X → is-∞-connected X
is-∞-connected-is-contr X is-contr-X k = is-connected-is-contr k is-contr-X
```

## Properties

### Being ∞-connected is invariant under equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-∞-connected-is-equiv :
    (f : A → B) → is-equiv f → is-∞-connected B → is-∞-connected A
  is-∞-connected-is-equiv f e is-∞-conn-B k =
    is-contr-is-equiv
      ( type-trunc k B)
      ( map-trunc k f)
      ( is-equiv-map-equiv-trunc k (f , e))
      ( is-∞-conn-B k)

  is-∞-connected-equiv :
    A ≃ B → is-∞-connected B → is-∞-connected A
  is-∞-connected-equiv f =
    is-∞-connected-is-equiv (pr1 f) (pr2 f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-∞-connected-equiv' : A ≃ B → is-∞-connected A → is-∞-connected B
  is-∞-connected-equiv' f = is-∞-connected-equiv (inv-equiv f)

  is-∞-connected-is-equiv' :
    (f : A → B) → is-equiv f → is-∞-connected A → is-∞-connected B
  is-∞-connected-is-equiv' f e = is-∞-connected-equiv' (f , e)
```
