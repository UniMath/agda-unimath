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

Consider two [cospans](foundation.cospans.md) `s := (X , f , g)` and
`t := (Y , h , k)` from `A` to `B`. A
{{#concept "morphism of cospans" Agda=hom-cospan}} from `s` to `t` consists of a
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
  (s : cospan l3 A B) (t : cospan l4 A B)
  where

  left-coherence-hom-cospan :
    (cospanning-type-cospan s → cospanning-type-cospan t) → UU (l1 ⊔ l4)
  left-coherence-hom-cospan h =
    coherence-triangle-maps (left-map-cospan t) h (left-map-cospan s)

  right-coherence-hom-cospan :
    (cospanning-type-cospan s → cospanning-type-cospan t) → UU (l2 ⊔ l4)
  right-coherence-hom-cospan h =
    coherence-triangle-maps (right-map-cospan t) h (right-map-cospan s)

  coherence-hom-cospan :
    (cospanning-type-cospan s → cospanning-type-cospan t) → UU (l1 ⊔ l2 ⊔ l4)
  coherence-hom-cospan f =
    left-coherence-hom-cospan f × right-coherence-hom-cospan f

  hom-cospan : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-cospan =
    Σ ( cospanning-type-cospan s → cospanning-type-cospan t)
      ( coherence-hom-cospan)

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : cospan l3 A B) (t : cospan l4 A B) (f : hom-cospan s t)
  where

  map-hom-cospan : cospanning-type-cospan s → cospanning-type-cospan t
  map-hom-cospan = pr1 f

  left-triangle-hom-cospan : left-coherence-hom-cospan s t map-hom-cospan
  left-triangle-hom-cospan = pr1 (pr2 f)

  right-triangle-hom-cospan : right-coherence-hom-cospan s t map-hom-cospan
  right-triangle-hom-cospan = pr2 (pr2 f)
```
