# Pushout products

```agda
module synthetic-homotopy-theory.pushout-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Consider two maps `f : A → X` and `g : B → Y`. The **pushout-product** `f □ g` of `f` and `g` is defined as the [cogap map](synthetic-homotopy-theory.pushouts.md) of the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
              f × id
       A × B --------> X × B
         |               |
  id × g |      H ⇗      | id × g
         V               V
       A × Y --------> X × Y.
              f × id
```

In other words, the pushout product is the unique map

```text
  f □ g : (X × B) ⊔_{A × B} (A × Y) → X × Y
```

equipped with [homotopies](foundation-core.homotopies.md)

```text
  K : (f □ g) ∘ inl ~ f × id
  L : (f □ g) ∘ inr ~ id × g
```

and a homotopy `M` witnessing that the [square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text

```

commutes. The pushout-products is often called the **fiberwise join**, because for each `(x , y) : X × Y` we have an [equivalence](foundation-core.equivalences.md)

```text
  fiber (f □ g) (x , y) ≃ (fiber f x) * (fiber g y).
```

from the [fibers](foundation-core.fibers-of-maps.md) of `f □ g` to the [join](synthetic-homotopy-theory.joins-of-types.md) of the fibers of `f` and `g`.

## Definitions

### The pushout-product

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  domain-pushout-product : UU {!!}
  domain-pushout-product = {!!}
```

## See also

- [The dependent pushout-product](synthetic-homotopy-theory.dependent-pushout-products.md)
