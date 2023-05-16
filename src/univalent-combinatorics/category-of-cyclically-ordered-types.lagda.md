# The category of cyclically ordered types

```agda
module univalent-combinatorics.category-of-cyclically-ordered-types where
```

<details><summary>Imports</summary>

```agda
```

</details>

## Idea

The **category `Λ` of cyclically ordered types** consists of:

- Objects are cyclically ordered sets of finite order.
- Morphisms are maps `C m → C n` such that for each point `x : C m` the induced map `L m → L n` on linear orders is order preserving.

The geometric realization of the categoy `Λ` should be `ℂP∞`.

It can also be described as the category of pairs `(M,U)` where `M` is a circle and `U` is a disjoint union of intervals in `M`. The morphisms from `(M,U)` to `(N,V)` are the oriented diffeomorphisms `φ : M → N` such that `φ U ⊆ V`.
