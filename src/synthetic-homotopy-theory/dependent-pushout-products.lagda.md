# Dependent pushout-products

```agda
module synthetic-homotopy-theory.dependent-pushout-products where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The _dependent pushout-product_ is a generalization of the
[pushout-product](synthetic-homotopy-theory.pushout-products.md). Consider a map
`f : A → B` and a family of maps `g : (x : X) → B x → Y x`. The
{{#concept "dependent pushout-product" Disambiguation="of maps of types" Agda=dependent-pushout-product}}
is the [cogap map](synthetic-homotopy-theory.pushouts.md) of the
[commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                       Σ f id
          Σ A (B ∘ f) --------> Σ X B
               |                  |
  Σ id (g ∘ f) |                  | Σ id g
               ∨                  ∨
          Σ A (Y ∘ f) --------> Σ X Y.
                       Σ f id
```

The [fiber](foundation-core.fibers-of-maps.md) of the dependent pushout product
at `(x , y)` is [equivalent](foundation-core.equivalences.md) to the join of
fibers

```text
  fiber f x * fiber (g x) y
```

A special case is of interest, where `Y` is the family of contractible types,
and `B` is a family of propositions.

## Definitions

### Dependent pushout-products

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {X : UU l2} {B : X → UU l3} {Y : X → UU l4}
  (f : A → X) (g : (x : X) → B x → Y x)
  where

  domain-dependent-pushout-product : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  domain-dependent-pushout-product =
    pushout
      ( map-Σ (Y ∘ f) id (g ∘ f))
      ( map-Σ B f (λ a → id))

  cocone-dependent-pushout-product :
    cocone
      ( map-Σ (Y ∘ f) id (g ∘ f))
      ( map-Σ B f (λ a → id))
      ( Σ X Y)
  pr1 cocone-dependent-pushout-product = map-Σ Y f (λ a → id)
  pr1 (pr2 cocone-dependent-pushout-product) = map-Σ Y id g
  pr2 (pr2 cocone-dependent-pushout-product) = refl-htpy

  abstract
    uniqueness-dependent-pushout-product :
      is-contr
        ( Σ ( domain-dependent-pushout-product → Σ X Y)
            ( λ h →
              htpy-cocone
                ( map-Σ (Y ∘ f) id (g ∘ f))
                ( map-Σ B f (λ a → id))
                ( cocone-map
                  ( map-Σ (Y ∘ f) id (g ∘ f))
                  ( map-Σ B f (λ a → id))
                  ( cocone-pushout
                    ( map-Σ (Y ∘ f) id (g ∘ f))
                    ( map-Σ B f (λ a → id)))
                  ( h))
                ( cocone-dependent-pushout-product)))
    uniqueness-dependent-pushout-product =
      uniqueness-map-universal-property-pushout
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ a → id))
        ( cocone-pushout (map-Σ (Y ∘ f) id (g ∘ f)) (map-Σ B f (λ a → id)))
        ( up-pushout (map-Σ (Y ∘ f) id (g ∘ f)) (map-Σ B f (λ a → id)))
        ( cocone-dependent-pushout-product)

  abstract
    dependent-pushout-product : domain-dependent-pushout-product → Σ X Y
    dependent-pushout-product =
      pr1 (center uniqueness-dependent-pushout-product)

    compute-inl-dependent-pushout-product :
      ( dependent-pushout-product ∘
        inl-pushout (map-Σ (Y ∘ f) id (g ∘ f)) (map-Σ B f (λ a → id))) ~
      ( map-Σ Y f (λ a → id))
    compute-inl-dependent-pushout-product =
      pr1 (pr2 (center uniqueness-dependent-pushout-product))

    compute-inr-dependent-pushout-product :
      ( dependent-pushout-product ∘
        inr-pushout (map-Σ (Y ∘ f) id (g ∘ f)) (map-Σ B f (λ a → id))) ~
      map-Σ Y id g
    compute-inr-dependent-pushout-product =
      pr1 (pr2 (pr2 (center uniqueness-dependent-pushout-product)))

    compute-glue-dependent-pushout-product :
      statement-coherence-htpy-cocone
        ( map-Σ (Y ∘ f) id (g ∘ f))
        ( map-Σ B f (λ a → id))
        ( cocone-map
          ( map-Σ (Y ∘ f) id (g ∘ f))
          ( map-Σ B f (λ a → id))
          ( cocone-pushout (map-Σ (Y ∘ f) id (g ∘ f)) (map-Σ B f (λ a → id)))
          ( dependent-pushout-product))
        ( cocone-dependent-pushout-product)
        ( compute-inl-dependent-pushout-product)
        ( compute-inr-dependent-pushout-product)
    compute-glue-dependent-pushout-product =
      pr2 (pr2 (pr2 (center uniqueness-dependent-pushout-product)))
```
