# Directed complete posets

```agda
module order-theory.directed-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.directed-families
open import order-theory.least-upper-bounds-posets
open import order-theory.posets
```

</details>

## Definition

```agda
is-directed-complete-poset-Prop :
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2) → Prop (l1 ⊔ l2 ⊔ lsuc l3)
is-directed-complete-poset-Prop l3 P =
  Π-Prop
    ( Inhabited-Type l3)
    ( λ I →
      Π-Prop
        ( type-Inhabited-Type I → element-Poset P)
        ( λ α →
          hom-Prop
            ( is-directed-family-poset-Prop P I α)
            ( has-least-upper-bound-family-poset-Prop P α)))

DCPO : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
DCPO l1 l2 l3 = type-subtype (is-directed-complete-poset-Prop {l1} {l2} l3)
```
