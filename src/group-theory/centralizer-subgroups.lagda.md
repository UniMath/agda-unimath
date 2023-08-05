# Centralizer subgroups

```agda
module group-theory.centralizer-subgroups where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider a [subset](group-theory.subsets-groups.md) `S` of a
[group](group-theory.groups.md) `G`. The **centralizer subgroup** `Cᴳ(S)` of `S`
is the subgroup of elements `g : G` such that `gs=sg` for every `s ∈ S`. In
other words, it consists of the elements of `G` that commute with all the
elements of `S`.

The definition of the centralizer is similar, but not identical to the
definition of the [normalizer](group-theory.normalizer-subgroups.md). There is
an inclusion of the centralizer into the normalizer, but not the other way
around.
