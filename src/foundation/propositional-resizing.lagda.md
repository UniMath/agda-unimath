# Propositional resizing

```agda
module foundation.propositional-resizing where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

We say that a universe `𝒱` satisfies `𝒰`-small
{{#concept "propositional resizing"}} if there is a type `Ω` in `𝒰`
[equipped](foundation.structure.md) with a
[subtype](foundation-core.subtypes.md) `Q` such that for each proposition `P` in
`𝒱` there is an element `u : Ω` such that `Q u ≃ P`. Such a type `Ω` is called
an `𝒰`-small {{#concept "classifier" Disambiguation="of small subobjects"}} of
`𝒱`-small subobjects.

## Definition

```agda
propositional-resizing : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
propositional-resizing l1 l2 =
  Σ ( Σ (UU l1) (subtype l1))
    ( λ Ω → (P : Prop l2) → Σ (pr1 Ω) (λ u → type-equiv-Prop (pr2 Ω u) P))
```

## See also

- [The large locale of propositions](foundation.large-locale-of-propositions.md)

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
