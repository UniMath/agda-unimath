# Cyclic types

```agda
module structured-types.cyclic-types where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

A **cyclic type** consists of a type `A` equipped with an automorphism
`e : A ≃ A` which is cyclic in the sense that

```text
  ∀ (x y : A), ∃ (k : ℤ), eᵏ x ＝ y.
```

Equivalently, a cyclic type is a
[connected set bundle](synthetic-homotopy-theory.connected-set-bundles-circle.md)
over the [circle](synthetic-homotopy-theory.circle.md).
