# Operations on spans of families of types

```agda
module foundation.operations-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.spans-families-of-types
open import foundation.universe-levels

open import foundation-core.function-types
```

</details>

## Idea

This file contains a collection of operations that produce new
[spans of families of types](foundation.spans-families-of-types.md) from given
spans of families of types.

## Definitions

### Concatenation of spans and families of maps

Consider a span `𝒮 := (S , s)` on a family of types `A : I → 𝒰` and consider a
family of maps `f : (i : I) → A i → B i`. Then we can concatenate the span `𝒮`
with the family of maps `f` to obtain the span `(S , λ i → f i ∘ s i)` on `B`.

```agda
module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  (𝒮 : span-type-family l4 A)
  (f : (i : I) → A i → B i)
  where

  spanning-type-concat-span-hom-family-of-types : UU l4
  spanning-type-concat-span-hom-family-of-types =
    spanning-type-span-type-family 𝒮

  map-concat-span-hom-family-of-types :
    (i : I) → spanning-type-concat-span-hom-family-of-types → B i
  map-concat-span-hom-family-of-types i =
    f i ∘ map-span-type-family 𝒮 i

  concat-span-hom-family-of-types :
    span-type-family l4 B
  pr1 concat-span-hom-family-of-types =
    spanning-type-concat-span-hom-family-of-types
  pr2 concat-span-hom-family-of-types =
    map-concat-span-hom-family-of-types
```
