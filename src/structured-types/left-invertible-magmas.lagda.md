# Left-invertible magmas

```agda
module structured-types.left-invertible-magmas where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.magmas
```

</details>

## Idea

A [magma](structured-types.magmas.md) `A` is
{{#concept "left-invertible" Disambiguation="magma" Agda=is-left-invertible-Magma}}
if the multiplication map `μ(a,-) : A → A` is an
[equivalence](foundation-core.equivalences.md) for every `a : A`. In other
words, if multiplying by a fixed element on the left is always an equivalence.

Left-invertibility appears as Definition 2.1(4) of {{#cite BCFR23}} in the
context of [H-spaces](structured-types.h-spaces.md).

## Definition

```agda
module _
  {l : Level} (A : Magma l)
  where

  is-left-invertible-Magma : UU l
  is-left-invertible-Magma = (a : type-Magma A) → is-equiv (mul-Magma A a)

  is-prop-is-left-invertible-Magma : is-prop is-left-invertible-Magma
  is-prop-is-left-invertible-Magma =
    is-prop-Π (λ a → is-property-is-equiv (mul-Magma A a))

  is-left-invertible-prop-Magma : Prop l
  is-left-invertible-prop-Magma =
    ( is-left-invertible-Magma , is-prop-is-left-invertible-Magma)
```

## References

{{#bibliography}}
