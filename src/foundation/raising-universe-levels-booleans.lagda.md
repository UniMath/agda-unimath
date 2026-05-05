# Raising universe levels of the booleans

```agda
module foundation.raising-universe-levels-booleans where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.booleans
open import foundation-core.equivalences
open import foundation-core.raising-universe-levels
```

</details>

## Idea

We can [raise](foundation.raising-universe-levels.md) the type of
[booleans](foundation-core.booleans.md) to any
[universe](foundation.universe-levels.md).

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
