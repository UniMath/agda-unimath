# Joins of maps

```agda
module synthetic-homotopy-theory.joins-of-maps where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider two maps `f : A → X` and `g : B → X` with a common codomain. The **join** `f * g` of `f` and `g` is defined as the [cogap map](synthetic-homotopy-theory.pushouts.md) of the [pullback square](foundation.pullbacks.md)

```text
             π₂
   A ×_X B -----> B
     |            |
  π₁ |            | g
     V            V
     A ---------> X.
           f
```

The join of maps is also called the **fiberwise join** because for each `x : X` we have an equivalence

```text
  fiber (f * g) x ≃ (fiber f x) * (fiber g x)
```

from the [fiber](foundation-core.fibers-of-maps.md) of `f * g` to the [join](synthetic-homotopy-theory.joins-of-types.md) of the fibers of `f` and `g`.  The join of maps is related to the [pushout-product](synthetic-homotopy-theory.pushout-products.md), because it fits in a [pullback diagram](foundation.pullback-squares.md)

```text
                 !
      A *_X B ------> (X × B) ⊔_{A × B} (A × Y)
        |                        |
  f * g |                        | f □ g
        V                        V
        X -------------------> X × X.
                 Δ
```
