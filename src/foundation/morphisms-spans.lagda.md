# Morphisms of spans

```agda
module foundation.morphisms-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.operations-spans
```

</details>

## Idea

A {{#concept "morphism of spans" Agda=hom-span}} from a
[span](foundation.spans.md) `A <-f- S -g-> B` to a span `A <-h- T -k-> B`
consists of a map `w : S → T` [equipped](foundation.structure.md) with two
[homotopies](foundation-core.homotopies.md) witnessing that the diagram

```text
             S
           ╱ │ ╲
        f ╱  │  ╲ h
         ∨   │   ∨
        A    │w   B
         ∧   │   ∧
        h ╲  │  ╱ k
           ╲ ∨ ╱
             T
```

[commutes](foundation.commuting-triangles-of-maps.md).

## Definitions

### Morphisms between spans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B) (t : span l4 A B)
  where

  left-coherence-hom-span :
    (spanning-type-span s → spanning-type-span t) → UU (l1 ⊔ l3)
  left-coherence-hom-span =
    coherence-triangle-maps (left-map-span s) (left-map-span t)

  right-coherence-hom-span :
    (spanning-type-span s → spanning-type-span t) → UU (l2 ⊔ l3)
  right-coherence-hom-span =
    coherence-triangle-maps (right-map-span s) (right-map-span t)

  coherence-hom-span :
    (spanning-type-span s → spanning-type-span t) → UU (l1 ⊔ l2 ⊔ l3)
  coherence-hom-span f = left-coherence-hom-span f × right-coherence-hom-span f

  hom-span : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-span = Σ (spanning-type-span s → spanning-type-span t) coherence-hom-span

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  (s : span l3 A B) (t : span l4 A B) (f : hom-span s t)
  where

  map-hom-span : spanning-type-span s → spanning-type-span t
  map-hom-span = pr1 f

  left-triangle-hom-span : left-coherence-hom-span s t map-hom-span
  left-triangle-hom-span = pr1 (pr2 f)

  right-triangle-hom-span : right-coherence-hom-span s t map-hom-span
  right-triangle-hom-span = pr2 (pr2 f)
```
