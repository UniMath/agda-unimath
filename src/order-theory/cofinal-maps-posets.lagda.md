# Cofinal maps in posets

```agda
module order-theory.cofinal-maps-posets where
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
{{#concept "cofinal" Disambiguation="map between posets" Agda=is-cofinal-map-Poset}}
if for any `b : B`, there [exists](foundation.existential-quantification.md) an
`a : A` such that `b ≤ f a`.

## Definition

```agda
module _
  {l1 l2 l3 : Level}
  {A : UU l1}
  (P : Poset l2 l3)
  (f : A → type-Poset P)
  where

  is-cofinal-prop-map-Poset : Prop (l1 ⊔ l2 ⊔ l3)
  is-cofinal-prop-map-Poset =
    Π-Prop
      ( type-Poset P)
      ( λ y → ∃ A (λ x → leq-prop-Poset P y (f x)))

  is-cofinal-map-Poset : UU (l1 ⊔ l2 ⊔ l3)
  is-cofinal-map-Poset = type-Prop is-cofinal-prop-map-Poset
```

## See also

- [Coinitial maps between posets](order-theory.coinitial-maps-posets.md)

## External links

- [Cofinal](<https://en.wikipedia.org/wiki/Cofinal_(mathematics)>) on Wikipedia
