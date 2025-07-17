# The Whitehead principle for types

```agda
module logic.whitehead-principle-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.dependent-pair-types
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

A type is said to be **∞-connected** if it is `n`-connected for all `n : 𝕋`.

Contractible types are ∞-connected.

The **Whitehead principle for types** asserts the converse, that ∞-connected
types are contractible.

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
is-contr-is-∞-connected : {l : Level} (X : UU l) → is-contr X → is-∞-connected X
is-contr-is-∞-connected X X-ctr k = is-connected-is-contr k X-ctr
```

### The Whitehead principle for types

```agda
Whitehead-Principle-Level : (l : Level) → UU (lsuc l)
Whitehead-Principle-Level l = (X : UU l) → is-∞-connected X → is-contr X

Whitehead-Principle : UUω
Whitehead-Principle = {l : Level} → Whitehead-Principle-Level l
```

## Properties

### Being ∞-connected is invariant under equivalence

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-∞-connected-is-equiv :
    (f : A → B) → is-equiv f → is-∞-connected B → is-∞-connected A
  is-∞-connected-is-equiv f e B-∞-conn k =
    is-contr-is-equiv (type-trunc k B) (map-trunc k f)
    ( is-equiv-map-equiv-trunc k (f , e)) (B-∞-conn k)

  is-∞-connected-equiv :
    A ≃ B → is-∞-connected B → is-∞-connected A
  is-∞-connected-equiv f B-∞-conn k =
    is-∞-connected-is-equiv (pr1 f) (pr2 f) B-∞-conn k

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-∞-connected-equiv' : A ≃ B → is-∞-connected A → is-∞-connected B
  is-∞-connected-equiv' f = is-∞-connected-equiv (inv-equiv f)

  is-∞-connected-is-equiv' :
    (f : A → B) → is-equiv f → is-∞-connected A → is-∞-connected B
  is-∞-connected-is-equiv' f e = is-∞-connected-equiv' (f , e)
```
