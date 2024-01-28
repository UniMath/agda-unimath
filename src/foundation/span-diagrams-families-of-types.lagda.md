# Span diagrams on families of types

```agda
module foundation.span-diagrams-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans-families-of-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "span diagram" Disambiguation="family of types"}} on a family of
types indexed by a type `I` consists of a type family `A : I → 𝒰`, and a
[span](foundation.spans-families-of-types.md) on the type family `A`. More
explicitly, a span diagram on a family of types indexed by `I` consists of a
type family `A : I → 𝒰`, a
{{#concept "spanning type" Disambiguation="span diagram on a family of types"}}
`S`, and a family of maps `f : (i : I) → S → A i`.

## Definitions

### Span diagrams of families of types

```agda
span-diagram-type-family :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
span-diagram-type-family l2 l3 I =
  Σ (I → UU l2) (λ A → span-type-family l3 A)

module _
  {l1 l2 l3 : Level} {I : UU l1} (s : span-diagram-type-family l2 l3 I)
  where

  family-span-diagram-type-family : I → UU l2
  family-span-diagram-type-family = pr1 s

  span-span-diagram-type-family :
    span-type-family l3 family-span-diagram-type-family
  span-span-diagram-type-family = pr2 s

  spanning-type-span-diagram-type-family : UU l3
  spanning-type-span-diagram-type-family =
    spanning-type-span-type-family
      ( span-span-diagram-type-family)

  map-span-diagram-type-family :
    (i : I) → spanning-type-span-diagram-type-family →
    family-span-diagram-type-family i
  map-span-diagram-type-family =
    map-span-type-family
      ( span-span-diagram-type-family)
```
