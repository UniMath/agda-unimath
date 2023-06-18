# Directed complete posets

```agda
module order-theory.directed-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.directed-families
open import order-theory.least-upper-bounds-posets
open import order-theory.posets
```

</details>

## Idea

A **DCPO**, i.e., a **directed complete partially ordered set**, is a poset in
which each directed family of elements has a least upper bound.

## Definition

```agda
is-directed-complete-Poset-Prop :
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2) → Prop (l1 ⊔ l2 ⊔ lsuc l3)
is-directed-complete-Poset-Prop l3 P =
  Π-Prop
    ( directed-family-Poset l3 P)
    ( λ x →
      has-least-upper-bound-family-of-elements-Poset-Prop P
        ( family-directed-family-Poset P x))

DCPO : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
DCPO l1 l2 l3 = type-subtype (is-directed-complete-Poset-Prop {l1} {l2} l3)
```
