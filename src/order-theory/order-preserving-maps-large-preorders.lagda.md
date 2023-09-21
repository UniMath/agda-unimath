# Order preserving maps between large preorders

```agda
module order-theory.order-preserving-maps-large-preorders where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import order-theory.large-preorders
```

</details>

## Idea

An order preserving map between large preorders from `P` to `Q` consists of a
map

```text
  f : type-Large-Preorder P l1 → type-Large-Preorder Q (γ l1)
```

for each universe level `l1`, such that `x ≤ y` implies `f x ≤ f y` for any two
elements `x y : P`.

## Definition

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  (γ : Level → Level)
  (P : Large-Preorder αP βP) (Q : Large-Preorder αQ βQ)
  where

  record hom-set-Large-Preorder : UUω
    where
    constructor
      make-hom-Large-Preorder
    field
      map-hom-Large-Preorder :
        {l1 : Level} → type-Large-Preorder P l1 → type-Large-Preorder Q (γ l1)
      preserves-order-hom-Large-Preorder :
        {l1 l2 : Level}
        (x : type-Large-Preorder P l1)
        (y : type-Large-Preorder P l2) →
        leq-Large-Preorder P x y →
        leq-Large-Preorder Q
          ( map-hom-Large-Preorder x)
          ( map-hom-Large-Preorder y)

  open hom-set-Large-Preorder public
```
