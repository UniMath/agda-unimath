# Nontrivial rings

```agda
module ring-theory.nontrivial-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.negation
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

Nontrivial rings are rings in which `0 ≠ 1`.

## Definition

```agda
is-nontrivial-ring-Prop : {l : Level} → Ring l → Prop l
is-nontrivial-ring-Prop R =
  neg-Prop (Id-Prop (set-Ring R) (zero-Ring R) (one-Ring R))

is-nontrivial-Ring : {l : Level} → Ring l → UU l
is-nontrivial-Ring R = type-Prop (is-nontrivial-ring-Prop R)

is-prop-is-nontrivial-Ring :
  {l : Level} (R : Ring l) → is-prop (is-nontrivial-Ring R)
is-prop-is-nontrivial-Ring R = is-prop-type-Prop (is-nontrivial-ring-Prop R)
```
