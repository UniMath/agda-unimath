# Raising universe levels of the booleans

```agda
module foundation.raising-universe-levels-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.raising-universe-levels
open import foundation.universe-levels

open import foundation-core.equivalences
```

</details>

## Idea

The type of **booleans** is a
[2-element type](univalent-combinatorics.2-element-types.md) with elements
`true false : bool`, which is used for reasoning with
[decidable propositions](foundation-core.decidable-propositions.md).

## Definition

### Raising universe levels of the booleans

```agda
raise-bool : (l : Level) → UU l
raise-bool l = raise l bool

raise-true : (l : Level) → raise-bool l
raise-true l = map-raise true

raise-false : (l : Level) → raise-bool l
raise-false l = map-raise false

compute-raise-bool : (l : Level) → bool ≃ raise-bool l
compute-raise-bool l = compute-raise l bool
```
