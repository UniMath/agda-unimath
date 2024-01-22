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

### Span diagrams of families of types

```agda
span-diagram-family-of-types :
  {l1 : Level} (l2 l3 : Level) → UU l1 → UU (l1 ⊔ lsuc l2 ⊔ lsuc l3)
span-diagram-family-of-types l2 l3 I =
  Σ (I → UU l2) (λ A → span-family-of-types l3 A)

module _
  {l1 l2 l3 : Level} {I : UU l1} (s : span-diagram-family-of-types l2 l3 I)
  where

  family-span-diagram-family-of-types : I → UU l2
  family-span-diagram-family-of-types = pr1 s

  span-family-of-types-span-diagram-family-of-types :
    span-family-of-types l3 family-span-diagram-family-of-types
  span-family-of-types-span-diagram-family-of-types = pr2 s

  spanning-type-span-diagram-family-of-types : UU l3
  spanning-type-span-diagram-family-of-types =
    spanning-type-span-family-of-types
      ( span-family-of-types-span-diagram-family-of-types)

  map-span-diagram-family-of-types :
    (i : I) → spanning-type-span-diagram-family-of-types →
    family-span-diagram-family-of-types i
  map-span-diagram-family-of-types =
    map-span-family-of-types
      ( span-family-of-types-span-diagram-family-of-types)
```

### Permutations of spans of families of types

Permutations of spans of families of types are a generalization of the opposite
of a binary span.

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2}
  where

  permutation-span-family-of-types :
    (e : I ≃ I) → span-family-of-types l3 A →
    span-family-of-types l3 (A ∘ map-equiv e)
  pr1 (permutation-span-family-of-types e s) =
    spanning-type-span-family-of-types s
  pr2 (permutation-span-family-of-types e s) i =
    map-span-family-of-types s (map-equiv e i)
```

## See also

- [(Binary) spans](foundation.spans.md)
