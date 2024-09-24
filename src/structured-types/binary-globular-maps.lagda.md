# Binary globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.binary-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

Consider three [globular types](structured-types.globular-types.md) `G`, `H`, and `K`. A {{#concept "binary globular map" Agda=binary-globular-map}} `f : G → H → K` consists of a binary map

```text
  f₀ : G₀ → H₀ → K₀
```

and for every `x x' : G₀`, `y y' : H₀` a binary globular map

```text
  f' : G' x x' → H' y y' → K (f x y) (f x' y')
```

on the `1`-cells of `G` and `H`.

## Definitions

### Binary globular maps

```agda
record
  binary-globular-map
    {l1 l2 l3 l4 l5 l6 : Level}
    (G : Globular-Type l1 l2) (H : Globular-Type l3 l4)
    (K : Globular-Type l5 l6) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
    where
    coinductive
    field
      0-cell-binary-globular-map :
        0-cell-Globular-Type G → 0-cell-Globular-Type H →
        0-cell-Globular-Type K
      1-cell-binary-globular-map-binary-globular-map :
        {x x' : 0-cell-Globular-Type G}
        {y y' : 0-cell-Globular-Type H} →
        binary-globular-map
          ( 1-cell-globular-type-Globular-Type G x x')
          ( 1-cell-globular-type-Globular-Type H y y')
          ( 1-cell-globular-type-Globular-Type K
            ( 0-cell-binary-globular-map x y)
            ( 0-cell-binary-globular-map x' y'))
```
