# Order preserving maps between large posets

```agda
module order-theory.order-preserving-maps-large-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.large-posets
open import order-theory.order-preserving-maps-large-preorders
```

</details>

## Idea

An order preserving map between large posets from `P` to `Q` consists of a map

```text
  f : type-Large-Poset P l1 → type-Large-Poset Q (γ l1)
```

for each universe level `l1`, such that `x ≤ y` implies `f x ≤ f y` for any two
elements `x y : P`.

## Definition

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  (γ : Level → Level)
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  hom-Large-Poset : UUω
  hom-Large-Poset =
    hom-Large-Preorder γ
      ( large-preorder-Large-Poset P)
      ( large-preorder-Large-Poset Q)

module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level} {γ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (f : hom-Large-Poset γ P Q)
  where

  map-hom-Large-Poset :
    {l1 : Level} → type-Large-Poset P l1 → type-Large-Poset Q (γ l1)
  map-hom-Large-Poset = map-hom-Large-Preorder f

  preserves-order-hom-Large-Poset :
    {l1 l2 : Level}
    (x : type-Large-Poset P l1) (y : type-Large-Poset P l2) →
    leq-Large-Poset P x y →
    leq-Large-Poset Q (map-hom-Large-Poset x) (map-hom-Large-Poset y)
  preserves-order-hom-Large-Poset =
    preserves-order-hom-Large-Preorder f
```
