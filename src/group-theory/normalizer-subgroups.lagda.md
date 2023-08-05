# Normalizer subgroups

```agda
module group-theory.normalizer-subgroups where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider a [subgroup](group-theory.subgroups.md) `H` of a
[group](group-theory.groups.md) `G`. The **normalizer subgroup** `Nᴳ(H)` of `G`
is the largest subgroup of `G` of which `H` is a
[normal subgroup](group-theory.normal-subgroups.md). The normalizer subgroup
consists of all elements `g : G` such that `gH = Hg`, and is itself a normal
subgroup of `G`.

Note: The normalizer subgroup should not be confused with the
[normal closure](group-theory.normal-closures-subgroups.md) of a subgroup, or
with the [normal core](group-theory.normal-cores-subgroups.md) of a subgroup.

## See also

- [Centralizer subgroups](group-theory.centralizer-subgroups.md)
- [Normal closures of subgroups](group-theory.normal-closures-subgroups.md)
- [Normal cores of subgroups](group-theory.normal-cores-subgroups.md)
