# Base changes of span diagrams

```agda
module foundation.base-changes-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-morphisms-span-diagrams
open import foundation.dependent-pair-types
open import foundation.span-diagrams
open import foundation.universe-levels
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮 := (A <-f- S -g-> B)`. A {{#concept "base change" Disambiguation="span diagram"}} of `𝒮` consists of a span diagram `𝒯` and a [cartesian morphism](foundation.cartesian-morphisms-span-diagrams.md) of span diagrams `𝒯 →ₓ 𝒮`.

## Definitions

### Base changes of span diagrams

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  base-change-span-diagram :
    (l4 l5 l6 : Level) → UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  base-change-span-diagram l4 l5 l6 =
    Σ (span-diagram l4 l5 l6) (λ 𝒯 → cartesian-hom-span-diagram 𝒯 𝒮)
```
