# Unbounded maps in posets

```agda
module order-theory.unbounded-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
open import foundation.existential-quantification
open import order-theory.posets
open import foundation.conjunction
open import foundation.propositions
```

</details>

## Idea

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1}
  (P : Poset l2 l3)
  (f : A → type-Poset P)
  where

  is-unbounded-above-prop-map-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  is-unbounded-above-prop-map-Poset =
    Π-Prop
      ( type-Poset P)
      ( λ y → ∃ A (λ x → leq-prop-Poset P y (f x)))

  is-unbounded-above-map-Poset : UU (l1 ⊔ l2 ⊔ l3)
  is-unbounded-above-map-Poset = type-Prop is-unbounded-above-prop-map-Poset

  is-unbounded-below-prop-map-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  is-unbounded-below-prop-map-Poset =
    Π-Prop
      ( type-Poset P)
      ( λ y → ∃ A (λ x → leq-prop-Poset P (f x) y))

  is-unbounded-below-map-Poset : UU (l1 ⊔ l2 ⊔ l3)
  is-unbounded-below-map-Poset = type-Prop is-unbounded-below-prop-map-Poset

  is-unbounded-above-and-below-prop-map-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  is-unbounded-above-and-below-prop-map-Poset =
    ( is-unbounded-above-prop-map-Poset) ∧
    ( is-unbounded-below-prop-map-Poset)

  is-unbounded-above-and-below-map-Poset : UU (l1 ⊔ l2 ⊔ l3)
  is-unbounded-above-and-below-map-Poset =
    type-Prop is-unbounded-above-and-below-prop-map-Poset
```
