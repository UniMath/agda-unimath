# Integer partitions

```agda
module elementary-number-theory.integer-partitions where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

An integer partition of a natural number n is a list of nonzero natural numbers
that sum up to n, up to reordering. We define the number `p n` of integer
partitions of `n` as the number of connected components in the type of finite
Ferrer diagrams of `Fin n`.
