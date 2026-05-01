# Coinitial maps in posets

```agda
module order-theory.coinitial-maps-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.existential-quantification
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A map between [posets](order-theory.posets.md) `f : A → B` is
{{#concept "coinitial" Disambiguation="map between posets" Agda=is-coinitial-map-Poset}}
if for any `b : B`, there [exists](foundation.existential-quantification.md) an
`a : A` such that `f a ≤ b`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1}
  (P : Poset l2 l3)
  (f : A → type-Poset P)
  where

  is-coinitial-prop-map-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  is-coinitial-prop-map-Poset =
    Π-Prop
      ( type-Poset P)
      ( λ y → ∃ A (λ x → leq-prop-Poset P (f x) y))

  is-coinitial-map-Poset : UU (l1 ⊔ l2 ⊔ l3)
  is-coinitial-map-Poset = type-Prop is-coinitial-prop-map-Poset
```

## See also

- [Cofinal maps between posets](order-theory.cofinal-maps-posets.md)
