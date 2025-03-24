# Spans of spans

```agda
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.spans-of-spans
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps funext univalence
open import foundation.dependent-pair-types
open import foundation.homotopies funext
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
```

</details>

## Idea

Given two [spans](foundation.spans.md) `F` and `G` from `A` to `B`

```text
  S ------> B
  | F       ∧
  |         |
  ∨       G |
  A <------ T,
```

then a {{#concept "span of spans" Disambiguation="of types" Agda=span-of-spans}}
from `F` to `G` is a span `S <--- W ---> T` such that the diagram

```text
  S ------> B
  |  ↖      ∧
  |    W    |
  ∨      ↘  |
  A <------ T
```

commutes.

## Definitions

### Spans of (binary) spans

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
  where

  coherence-left-span-of-spans :
    {l : Level} (𝒮 : span l3 A B) (𝒯 : span l4 A B) →
    span l (spanning-type-span 𝒮) (spanning-type-span 𝒯) → UU (l1 ⊔ l)
  coherence-left-span-of-spans {l} 𝒮 𝒯 F =
    coherence-square-maps
      ( left-map-span F)
      ( right-map-span F)
      ( left-map-span 𝒮)
      ( left-map-span 𝒯)

  coherence-right-span-of-spans :
    {l : Level} (𝒮 : span l3 A B) (𝒯 : span l4 A B) →
    span l (spanning-type-span 𝒮) (spanning-type-span 𝒯) → UU (l2 ⊔ l)
  coherence-right-span-of-spans {l} 𝒮 𝒯 F =
    coherence-square-maps
      ( left-map-span F)
      ( right-map-span F)
      ( right-map-span 𝒮)
      ( right-map-span 𝒯)

  coherence-span-of-spans :
    {l : Level} (𝒮 : span l3 A B) (𝒯 : span l4 A B) →
    span l (spanning-type-span 𝒮) (spanning-type-span 𝒯) → UU (l1 ⊔ l2 ⊔ l)
  coherence-span-of-spans 𝒮 𝒯 F =
    ( coherence-left-span-of-spans 𝒮 𝒯 F) ×
    ( coherence-right-span-of-spans 𝒮 𝒯 F)

  span-of-spans :
    (l : Level) → span l3 A B → span l4 A B → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ lsuc l)
  span-of-spans l 𝒮 𝒯 =
    Σ ( span l (spanning-type-span 𝒮) (spanning-type-span 𝒯))
      ( coherence-span-of-spans 𝒮 𝒯)

module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (𝒮 : span l3 A B) (𝒯 : span l4 A B)
  (F : span-of-spans l5 𝒮 𝒯)
  where

  span-span-of-spans : span l5 (spanning-type-span 𝒮) (spanning-type-span 𝒯)
  span-span-of-spans = pr1 F

  spanning-type-span-of-spans : UU l5
  spanning-type-span-of-spans = spanning-type-span span-span-of-spans

  left-map-span-of-spans : spanning-type-span-of-spans → spanning-type-span 𝒮
  left-map-span-of-spans = left-map-span span-span-of-spans

  right-map-span-of-spans : spanning-type-span-of-spans → spanning-type-span 𝒯
  right-map-span-of-spans = right-map-span span-span-of-spans

  coh-span-of-spans : coherence-span-of-spans 𝒮 𝒯 span-span-of-spans
  coh-span-of-spans = pr2 F

  coh-left-span-of-spans :
    coherence-square-maps
      ( left-map-span-of-spans)
      ( right-map-span-of-spans)
      ( left-map-span 𝒮)
      ( left-map-span 𝒯)
  coh-left-span-of-spans = pr1 coh-span-of-spans

  coh-right-span-of-spans :
    coherence-square-maps
      ( left-map-span-of-spans)
      ( right-map-span-of-spans)
      ( right-map-span 𝒮)
      ( right-map-span 𝒯)
  coh-right-span-of-spans = pr2 coh-span-of-spans
```

### Identity spans of spans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  (𝒮 : span l3 A B)
  where

  id-span-of-spans : span-of-spans l3 𝒮 𝒮
  id-span-of-spans = id-span , refl-htpy , refl-htpy
```
