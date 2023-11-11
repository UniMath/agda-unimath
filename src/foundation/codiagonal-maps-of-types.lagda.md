# Codiagonal maps of types

```agda
{-# OPTIONS --cubical-compatible #-}

module foundation.codiagonal-maps-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import foundation-core.coproduct-types
```

</details>

## Idea

The codiagonal map `∇ : A + A → A` of `A` is the map that projects `A + A` onto
`A`.

## Definitions

```agda
module _
  { l1 : Level} (A : UU l1)
  where

  codiagonal : A + A → A
  codiagonal (inl a) = a
  codiagonal (inr a) = a
```
