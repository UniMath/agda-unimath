# Diagonals of morphisms of arrows

```agda
module foundation.diagonals-of-morphisms-arrows where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

The {{#concept "diagonal" Disambiguation="morphism of arrows"}} of a
[morphism of arrows](foundation.morphisms-arrows.md)

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

is obtained by taking the [diagonals](foundation.diagonals-of-maps.md) of the
maps `i` and `j`, which fit in a naturality square

```text
       Δ i
    A -----> A ×_X A
    |           |
  f |           | functoriality Δ g
    ∨           ∨
    B -----> B ×_Y B.
       Δ j
```

In other words, the diagonal of a morphism of arrows `h : hom-arrow f g` is a
morphism of arrows `Δ h : hom-arrow f (functoriality Δ g)`.

Note that this operation preserves
[cartesian squares](foundation.cartesian-morphisms-arrows.md). Furthermore, by a
lemma of [David Wärn](https://ncatlab.org/nlab/show/David+Wärn) it also follows
that this operation preserves
[cocartesian morphisms of arrows](synthetic-homotopy-theory.cocartesian-morphisms-arrows.md)
out of [embeddings](foundation.embeddings.md).
