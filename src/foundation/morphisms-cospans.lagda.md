# Morphisms of cospans

```agda
module foundation.morphisms-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.commuting-triangles-of-maps
```

</details>

## Idea

Consider two [cospans](foundation.cospans.md) `c := (X , f , g)` and
`d := (Y , h , k)` from `A` to `B`. A
{{#concept "morphism of cospans" Agda=hom-cospan}} from `c` to `d` consists of a
map `u : X → Y` equipped with [homotopies](foundation-core.homotopies.md)
witnessing that the two triangles

```text
      u              u
  X ----> Y      X ----> Y
   \     /        \     /
  f \   / h      g \   / k
     ∨ ∨            ∨ ∨
      A              B
```

[commute](foundation.commuting-triangles-of-maps.md).

## Definitions

### Morphisms of cospans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (c : cospan l3 A B) (d : cospan l4 A B)
  where

  coherence-hom-cospan :
    (cospanning-type-cospan c → cospanning-type-cospan d) → UU (l1 ⊔ l2 ⊔ l4)
  coherence-hom-cospan h =
    ( coherence-triangle-maps (left-map-cospan d) h (left-map-cospan c)) ×
    ( coherence-triangle-maps (right-map-cospan d) h (right-map-cospan c))

  hom-cospan : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-cospan =
    Σ ( cospanning-type-cospan c → cospanning-type-cospan d)
      ( coherence-hom-cospan)
```
