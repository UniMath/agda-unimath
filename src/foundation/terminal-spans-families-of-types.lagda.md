# Terminal spans on families of types

```agda
module foundation.terminal-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.morphisms-spans-families-of-types
open import foundation.spans-families-of-types
open import foundation.universe-levels

open import foundation-core.contractible-types
```

</details>

## Idea

A [span](foundation.spans-families-of-types.md) `𝒮` on a family of types
`A : I → 𝒰` is said to be
{{#concept "terminal" Disambiguation="span on a family of types" Agda=is-terminal-span-type-family}}
if for each span `𝒯` on `A` the type of
[morphisms of spans](foundation.morphisms-spans-families-of-types.md) `𝒯 → 𝒮` is
[contractible](foundation-core.contractible-types.md).

## Definitions

### The predicate of being a terminal span on a family of types

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} (𝒮 : span-type-family l3 A)
  where

  is-terminal-span-type-family : UUω
  is-terminal-span-type-family =
    {l : Level} (𝒯 : span-type-family l A) →
    is-contr (hom-span-type-family 𝒯 𝒮)
```

## See also

- [The universal property of dependent function types](foundation.universal-property-dependent-function-types.md)
  is equivalent to the condition of being a terminal span of families of types.
