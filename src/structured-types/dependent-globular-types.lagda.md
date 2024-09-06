# Dependent globular types

```agda
{-# OPTIONS --guardedness #-}

module structured-types.dependent-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import structured-types.globular-types
```

</details>

## Idea

Consider a [globular type](structured-types.globular-types.md) `G`. A
{{#concept "dependent globular type" Agda=Dependent-Globular-Type}} over `G`
consists of a type family `H₀ : G₀ → 𝒰`, and for any two `0`-cells `x y : G₀` in
`G` a binary family of dependent globular types

```text
  H₁ : H₀ x → H₀ y → dependent-globular-type (G₁ x y).
```

## Definitions

### Dependent globular types

```agda
record
  Dependent-Globular-Type
    {l1 l2 : Level} (l3 l4 : Level) (G : Globular-Type l1 l2) :
    UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
  where
  coinductive
  field
    0-cell-Dependent-Globular-Type :
      0-cell-Globular-Type G → UU l3
    1-cell-dependent-globular-type-Dependent-Globular-Type :
      {x y : 0-cell-Globular-Type G} →
      0-cell-Dependent-Globular-Type x →
      0-cell-Dependent-Globular-Type y →
      Dependent-Globular-Type l4 l4 (1-cell-globular-type-Globular-Type G x y)

open Dependent-Globular-Type public

module _
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G)
  where

  1-cell-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type G} →
    (y : 0-cell-Dependent-Globular-Type H x)
    (y' : 0-cell-Dependent-Globular-Type H x') →
    1-cell-Globular-Type G x x' → UU l4
  1-cell-Dependent-Globular-Type y y' =
    0-cell-Dependent-Globular-Type
      ( 1-cell-dependent-globular-type-Dependent-Globular-Type H y y')
```

## See also

- [Dependent reflexive globular types](structured-types.dependent-reflexive-globular-types.md)
