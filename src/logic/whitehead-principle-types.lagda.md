# The Whitehead principle for types

```agda
module logic.whitehead-principle-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-types
open import foundation.dependent-pair-types
open import foundation.truncation-levels
open import foundation.universe-levels

open import foundation-core.contractible-types
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
Whitehead-Principle : (l : Level) → UU (lsuc l)
Whitehead-Principle l = (X : UU l) → is-∞-connected X → is-contr X
```
