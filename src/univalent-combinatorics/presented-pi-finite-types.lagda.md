# Finitely π-presented types

```agda
module univalent-combinatorics.presented-pi-finite-types where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

A type `A` is said to be finitely `π₀`-presented if there is a standard pruned
tree `T` of height 1 so that `A` has a presentation of cardinality `width T`,
and `A` is said to be finitely `πₙ₊₁`-presented if there is a standard pruned
tree `T` of height `n+2` and a map `f : Fin (width T) → A` so that
`η ∘ f : Fin (width T) → ║A║₀` is an equivalence, and for each
`x : Fin (width T)` the type `Ω (A, f x)` is
