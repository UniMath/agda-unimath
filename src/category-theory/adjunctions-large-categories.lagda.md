# Adjunctions between large categories

```agda
module category-theory.adjunctions-large-categories where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Let `C` and `D` be two
[large categories](category-theory.large-categories.md). Two
[functors](category-theory.functors-large-categories.md) `F : C → D` and
`G : D → C` constitute an **adjoint pair** if

- for each pair of objects `X` in `C` and `Y` in `D`, there is an
  [equivalence](foundation-core.equivalences.md)
  `ϕ X Y : hom X (G Y) ≃ hom (F X) Y` such that
- for every pair of morhpisms `f : X₂ → X₁` and `g : Y₁ → Y₂` the following
  square commutes:

```text
                        ϕ X₁ Y₁
         hom X₁ (G Y₁) --------> hom (F X₁) Y₁
              |                        |
  G g ∘ _ ∘ f |                        | g ∘ _ ∘ F f
              |                        |
              v                        v
         hom X₂ (G Y₂) --------> hom (F X₂) Y₂
                        ϕ X₂ Y₂
```

In this case we say that `F` is **left adjoint** to `G` and `G` is **right
adjoint** to `F` and write this as `F ⊣ G`.
