# Composition structure on globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.composition-structure-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.binary-globular-maps
open import globular-types.globular-types
```

</details>

## Idea

A
{{#concept "composition structure" Disambiguation="globular type" Agda=composition-Globular-Type}}
on a [globular type](globular-types.globular-types.md) `G` consists of a
[binary globular map](globular-types.binary-globular-maps.md)

```text
  - ∘ - : G' y z → G' x y → G' x z,
```

and for any two `0`-cells `x y : G₀` a composition structure on the globular
type `G' x y` of `1`-cells of `G`. More explicitly, a composition structure
consists of binary operations

```text
  - ∘ - : (𝑛+1)-Cell G y z → (𝑛+1)-Cell G x y → (𝑛+1)-Cell G x z,
```

each of which preserve all higher cells of the globular type `G`. Globular
composition structure is therefore a strengthening of the
[transitivity structure](globular-types.transitive-globular-types.md) on
globular types.

## Definitions

### Globular composition structure

```agda
record
  composition-Globular-Type
    {l1 l2 : Level} (G : Globular-Type l1 l2) : UU (l1 ⊔ l2)
  where
  coinductive

  field
    comp-binary-globular-map-composition-Globular-Type :
      {x y z : 0-cell-Globular-Type G} →
      binary-globular-map
        ( 1-cell-globular-type-Globular-Type G y z)
        ( 1-cell-globular-type-Globular-Type G x y)
        ( 1-cell-globular-type-Globular-Type G x z)

  field
    composition-1-cell-globular-type-Globular-Type :
      {x y : 0-cell-Globular-Type G} →
      composition-Globular-Type
        ( 1-cell-globular-type-Globular-Type G x y)

open composition-Globular-Type public
```
