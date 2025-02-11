# Spans of families of types

```agda
module foundation.spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
```

</details>

## Idea

Consider a family of types `A i` indexed by `i : I`. A
{{#concept "span" Disambiguation="family of types" Agda=span-type-family}} on
`A` consists of a type `S` equipped with a family of maps

```text
  (i : I) → S → A i.
```

The type `S` is called the
{{#concept "spanning type" Disambiguation="span of family of types" Agda=spanning-type-span-type-family}}
of the span.

## Definitions

### Spans on families of types

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (A : I → UU l2)
  where

  span-type-family : UU (l1 ⊔ l2 ⊔ lsuc l3)
  span-type-family = Σ (UU l3) (λ S → (i : I) → S → A i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  (s : span-type-family l3 A)
  where

  spanning-type-span-type-family : UU l3
  spanning-type-span-type-family = pr1 s

  map-span-type-family :
    (i : I) → spanning-type-span-type-family → A i
  map-span-type-family = pr2 s
```

## See also

- [(Binary) spans](foundation.spans.md)
- [Span diagrams on families of types](foundation.span-diagrams-families-of-types.md)
- [Permutations of spans of on families of types](foundation.permutations-spans-families-of-types.md)
