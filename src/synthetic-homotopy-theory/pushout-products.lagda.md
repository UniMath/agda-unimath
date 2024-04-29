# Pushout-products

```agda
module synthetic-homotopy-theory.pushout-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

Consider two maps `f : A → X` and `g : B → Y`. The **pushout-product** `f □ g`
of `f` and `g` is defined as the
[cogap map](synthetic-homotopy-theory.pushouts.md) of the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
              f × id
       A × B --------> X × B
         |               |
  id × g |      H ⇗      | id × g
         ∨               ∨
       A × Y --------> X × Y.
              f × id
```

In other words, the pushout-product is the unique map

```text
  f □ g : (X × B) ⊔_{A × B} (A × Y) → X × Y
```

equipped with [homotopies](foundation-core.homotopies.md)

```text
  K : (f □ g) ∘ inl ~ f × id
  L : (f □ g) ∘ inr ~ id × g
```

and a homotopy `M` witnessing that the
[square of homotopies](foundation.commuting-squares-of-homotopies.md)

```text
                                 K ·r (id × g)
       (f □ g) ∘ inl ∘ (id × g) ---------------> (f × id) ∘ (id × g)
                  |                                       |
  (f □ g) ·l glue |                                       | H
                  |                                       |
                  ∨                                       ∨
       (f □ g) ∘ inr ∘ (f × id) ---------------> (id × g) ∘ (f × id)
                                 L ·r (f × id)
```

commutes. The pushout-products is often called the **fiberwise join**, because
for each `(x , y) : X × Y` we have an
[equivalence](foundation-core.equivalences.md)

```text
  fiber (f □ g) (x , y) ≃ (fiber f x) * (fiber g y).
```

from the [fibers](foundation-core.fibers-of-maps.md) of `f □ g` to the
[join](synthetic-homotopy-theory.joins-of-types.md) of the fibers of `f` and
`g`.

There is an "adjoint relation" between the pushout-product and the
[pullback-hom](orthogonal-factorization-systems.pullback-hom.md): For any three
maps `f`, `g`, and `h` we have an
[equivalence of maps](foundation.equivalences-arrows.md)

```text
  ⟨f □ g , h⟩ ≃ ⟨f , ⟨g , h⟩⟩.
```

## Definitions

### The pushout-product

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → X) (g : B → Y)
  where

  domain-pushout-product : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  domain-pushout-product =
    pushout (map-product id g) (map-product f id)

  cocone-pushout-product : cocone (map-product id g) (map-product f id) (X × Y)
  pr1 cocone-pushout-product = map-product f id
  pr1 (pr2 cocone-pushout-product) = map-product id g
  pr2 (pr2 cocone-pushout-product) = coherence-square-map-product f g

  abstract
    uniqueness-pushout-product :
      is-contr
        ( Σ ( domain-pushout-product → X × Y)
            ( λ h →
              htpy-cocone
                ( map-product id g)
                ( map-product f id)
                ( cocone-map
                  ( map-product id g)
                  ( map-product f id)
                  ( cocone-pushout (map-product id g) (map-product f id))
                  ( h))
                ( cocone-pushout-product)))
    uniqueness-pushout-product =
      uniqueness-map-universal-property-pushout
        ( map-product id g)
        ( map-product f id)
        ( cocone-pushout (map-product id g) (map-product f id))
        ( up-pushout (map-product id g) (map-product f id))
        ( cocone-pushout-product)

  abstract
    pushout-product : domain-pushout-product → X × Y
    pushout-product = pr1 (center uniqueness-pushout-product)

    compute-inl-pushout-product :
      pushout-product ∘ inl-pushout (map-product id g) (map-product f id) ~
      map-product f id
    compute-inl-pushout-product =
      pr1 (pr2 (center uniqueness-pushout-product))

    compute-inr-pushout-product :
      pushout-product ∘ inr-pushout (map-product id g) (map-product f id) ~
      map-product id g
    compute-inr-pushout-product =
      pr1 (pr2 (pr2 (center uniqueness-pushout-product)))

    compute-glue-pushout-product :
      statement-coherence-htpy-cocone
        ( map-product id g)
        ( map-product f id)
        ( cocone-map
          ( map-product id g)
          ( map-product f id)
          ( cocone-pushout (map-product id g) (map-product f id))
          ( pushout-product))
        ( cocone-pushout-product)
        ( compute-inl-pushout-product)
        ( compute-inr-pushout-product)
    compute-glue-pushout-product =
      pr2 (pr2 (pr2 (center uniqueness-pushout-product)))
```

## Properties

### The adjoint relation between pushout-products and pullback-homs

For any three maps `f`, `g`, and `h` we have an adjoint relation

```text
  hom-arrow (f □ g) h ≃ hom-arrow f ⟨g , h⟩
```

that extends to an equivalence of maps

```text
  ⟨f □ g , h⟩ ≃ ⟨f , ⟨g , h⟩⟩.
```

This remains to be formalized.

## See also

- [The dependent pushout-product](synthetic-homotopy-theory.dependent-pushout-products.md)

## External links

- [Pushout-product](https://ncatlab.org/nlab/show/pushout-product) at $n$lab

A wikidata identifier for this concept is not available.
