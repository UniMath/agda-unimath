---
title: Connected types
---

```agda
module foundation.connected-types where

open import foundation.contractible-types
open import foundation.propositions
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.universe-levels
```

## Idea

A type is said to be **`k`-connected** if its `k`-truncation is contractible.

## Definition

```agda
is-connected-Prop : {l : Level} (k : 𝕋) → UU l → UU-Prop l
is-connected-Prop k A = is-contr-Prop (type-trunc k A)

is-connected : {l : Level} (k : 𝕋) → UU l → UU l
is-connected k A = type-Prop (is-connected-Prop k A)

is-prop-is-connected :
  {l : Level} (k : 𝕋) (A : UU l) → is-prop (is-connected k A)
is-prop-is-connected k A = is-prop-type-Prop (is-connected-Prop k A)
```
