# Propositional resizing

```agda
module foundation.propositional-resizing where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.law-of-excluded-middle
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
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

## TODO

```agda
module _
  {l1 l2 : Level} ((Ω , prop-resize) : propositional-resizing l1 l2)
  where

  resize : Prop l2 → Prop l1
  resize P = pr2 Ω (pr1 (prop-resize P))

  is-equiv-resize : (P : Prop l2) → type-equiv-Prop (resize P) P
  is-equiv-resize P = pr2 (prop-resize P)

unit-equiv-true :
  {l : Level} (P : Prop l) → type-Prop P → type-equiv-Prop unit-Prop P
pr1 (unit-equiv-true P p) _ = p
pr2 (unit-equiv-true P p) =
  is-equiv-is-prop is-prop-unit (is-prop-type-Prop P) (λ _ → star)

empty-equiv-false :
  {l : Level} (P : Prop l) → ¬ (type-Prop P) → type-equiv-Prop empty-Prop P
pr1 (empty-equiv-false P np) = ex-falso
pr2 (empty-equiv-false P np) =
  is-equiv-is-prop is-prop-empty (is-prop-type-Prop P) np

propositional-resizing-LEM :
  (l1 : Level) {l2 : Level} → LEM l2 → propositional-resizing l1 l2
pr1 (pr1 (propositional-resizing-LEM l1 lem)) = raise-unit l1 + raise-unit l1
pr2 (pr1 (propositional-resizing-LEM l1 lem)) (inl _) = raise-unit-Prop l1
pr2 (pr1 (propositional-resizing-LEM l1 lem)) (inr _) = raise-empty-Prop l1
pr2 (propositional-resizing-LEM l1 lem) P with lem P
... | inl p =
  pair
    ( inl raise-star)
    ( unit-equiv-true P p ∘e inv-equiv (compute-raise l1 unit))
... | inr np =
  pair
    ( inr raise-star)
    ( empty-equiv-false P np ∘e inv-equiv (compute-raise l1 empty))
```

## See also

- [The large locale of propositions](foundation.large-locale-of-propositions.md)

## Table of files about propositional logic

The following table gives an overview of basic constructions in propositional
logic and related considerations.

{{#include tables/propositional-logic.md}}
