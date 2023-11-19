# Dependent pushout-products

```agda
module synthetic-homotopy-theory.dependent-pushout-products where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

The **dependent pushout-product** is a generalization of the [pushout-product](synthetic-homotopy-theory.pushout-products.md). Consider a map `f : A → B` and a family of maps `g : (x : X) → B x → Y x`. The **dependent pushout-procuct** is the [cogap map](synthetic-homotopy-theory.pushouts.md) of the [commuting square](foundation-core.commuting-squares-of-maps.md)

```text
                 Σ id (g ∘ f)
    Σ A (B ∘ f) --------------> Σ A (Y ∘ f)
         |                        |
  Σ f id |                        | Σ f id
         V                        V
       Σ X B -----------------> Σ X Y
                   Σ id g
```

