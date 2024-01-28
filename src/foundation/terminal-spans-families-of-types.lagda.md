# Terminal spans on families of types

```agda
module foundation.terminal-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.morphisms-spans-families-of-types
open import foundation.spans-families-of-types
open import foundation.universe-levels
```

</details>

## Idea

A [span](foundation.spans-families-of-types.md) `𝒮` on a family of types `A : I → 𝒰` is said to be {{#concept "terminal" Disambiguation="span on a family of types" Agda=is-terminal-span-family-of-types}} if for each span `𝒯` on `A` the type of [morphisms of spans](foundation.morphisms-spans-families-of-types.md) `𝒯 → 𝒮` is [contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate of being a terminal span on a family of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (𝒮 : span-family-of-types l3 A)
  where

  is-terminal-span-family-of-types : UUω
  is-terminal-span-family-of-types =
    {l : Level} (𝒯 : span-family-of-types l A) →
    is-contr (hom-span-family-of-types 𝒯 𝒮)
```
