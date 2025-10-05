# Filters on posets

```agda
module order-theory.filters-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.lower-bounds-posets
open import order-theory.posets
open import order-theory.subposets
```

</details>

## Idea

A {{#concept "filter" WDID=Q1052692 WD="filter" Agda=Filter-Poset}} of a
[poset](order-theory.posets.md) `P` is a [subposet](order-theory.subposets.md)
`F` of `P` with the following properties:

- [Inhabitedness](foundation.inhabited-subtypes.md): `F` is inhabited.
- Downward directedness: any two elements of `F` have a
  [lower bound](order-theory.lower-bounds-posets.md) in `F`.
- Upward closure: if `x ∈ F`, `p ∈ P`, and `x ≤ p`, then `p ∈ F`.

## Definition

```agda
module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (F : Subposet l3 P)
  where

  is-downward-directed-prop-Subposet : Prop (l1 ⊔ l2 ⊔ l3)
  is-downward-directed-prop-Subposet =
    Π-Prop
      ( type-Subposet P F)
      ( λ x →
        Π-Prop
          ( type-Subposet P F)
          ( λ y →
            ∃ ( type-Subposet P F)
              ( is-binary-lower-bound-Poset-Prop (poset-Subposet P F) x y)))

  is-downward-directed-Subposet : UU (l1 ⊔ l2 ⊔ l3)
  is-downward-directed-Subposet = type-Prop is-downward-directed-prop-Subposet

  is-upward-closed-prop-Subposet : Prop (l1 ⊔ l2 ⊔ l3)
  is-upward-closed-prop-Subposet =
    Π-Prop
      ( type-Subposet P F)
      ( λ (x , x∈F) → leq-prop-subtype (leq-prop-Poset P x) F)

  is-upward-closed-Subposet : UU (l1 ⊔ l2 ⊔ l3)
  is-upward-closed-Subposet = type-Prop is-upward-closed-prop-Subposet

  is-filter-prop-Subposet : Prop (l1 ⊔ l2 ⊔ l3)
  is-filter-prop-Subposet =
    is-inhabited-subtype-Prop F ∧ is-downward-directed-prop-Subposet ∧
    is-upward-closed-prop-Subposet

  is-filter-Subposet : UU (l1 ⊔ l2 ⊔ l3)
  is-filter-Subposet = type-Prop is-filter-prop-Subposet

Filter-Poset :
  {l1 l2 : Level} → (l : Level) → Poset l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l)
Filter-Poset l P = type-subtype (is-filter-prop-Subposet {l3 = l} P)
```

## External links

- [Filter (mathematics)](<https://en.wikipedia.org/wiki/Filter_(mathematics)>)
  at Wikipedia
- [filter] at $n$Lab
