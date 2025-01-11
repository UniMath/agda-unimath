# Finite maps into the natural numbers

```agda
module elementary-number-theory.finite-maps-natural-numbers where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

A map $f : A \to \mathbb{N}$ is said to be a {{#concept "finite map" Disambiguation="natural numbers"}} if its [fibers](foundation-core.finite-types.md) are [finite](univalent-combinatorics.finite-types.md).

Finite maps are [decidable](elementary-number-theory.decidable-maps-natural-numbers.md). Every finite map $f : \mathbb{N} \to \mathbb{N}$ has a definite lowest value, and for every finite map $f : \mathbb{N} \to \mathbb{N}$ that takes a value below $B$ there is a largest number $k$ such that $f(k) \leq b$.
