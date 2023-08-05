# Normal cores of subgroups

```agda
module group-theory.normal-cores-subgroups where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider a [subgroup](group-theory.subgroups.md) `H` of a
[group](group-theory.groups.md) `G`. The **normal core** of `H` is the largest
[normal subgroup](group-theory.normal-subgroups.md) of `G` that is contained in
`H`. It is equivalently described as the intersection of all
[conjugates](group-theory.conjugation.md) of `H`.

In other words, the normal core operation is the upper adjoint in a
[Galois connection](order-theory.galois-connections-large-posets.md) between the
[large poset](order-theory.large-posets.md) of subgroups of `G` and normal
subgroups of `G`. The lower adjoint of this Galois connection is the inclusion
function from normal subgroups to subgroups of `G`.

Note: The normal core should not be confused with the
[normalizer](group-theory.normalizer-subgroups.md) of a subgroup, or with the
[normal closure](group-theory.normal-closures-subgroups.md) of a subgroup.

## See also

- [Centralizer subgroups](group-theory.centralizer-subgroups.md)
- [Normal closures of subgroups](group-theory.normal-closures-subgroups.md)
- [Normalizers of subgroups](group-theory.normalizer-subgroups.md)
