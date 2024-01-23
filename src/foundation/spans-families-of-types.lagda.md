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
{{#concept "span" Disambiguation="family of types" Agda=span-family-of-types}}
on `A` consists of a type `S` equipped with a family of maps

```text
  (i : I) → S → A i.
```

The type `S` is called the
{{#concept "spanning type" Disambiguation="span of family of types" Agda=spanning-type-span-family-of-types}}
of the span.

## Definitions

### Spans on families of types

```agda
module _
  {l1 l2 : Level} (l3 : Level) {I : UU l1} (A : I → UU l2)
  where

  span-family-of-types : UU (l1 ⊔ l2 ⊔ lsuc l3)
  span-family-of-types = Σ (UU l3) (λ S → (i : I) → S → A i)

module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  (s : span-family-of-types l3 A)
  where

  spanning-type-span-family-of-types : UU l3
  spanning-type-span-family-of-types = pr1 s

  map-span-family-of-types :
    (i : I) → spanning-type-span-family-of-types → A i
  map-span-family-of-types = pr2 s
```

## See also

- [(Binary) spans](foundation.spans.md)
- [Span diagrams on families of types](foundation.span-diagrams-families-of-types.md)
- [Permutations of spans of on families of types](foundation.permuations-spans-families-of-types.md)
