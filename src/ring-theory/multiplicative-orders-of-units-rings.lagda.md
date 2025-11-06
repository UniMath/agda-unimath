# Multiplicative orders of elements of rings

```agda
module ring-theory.multiplicative-orders-of-units-rings where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

The
{{#concept "multiplicative order" Disambiguation="of an invertible element of a ring"}}
of an [invertible element](ring-theory.invertible-elements-rings.md) `x` of a
[ring](ring-theory.rings.md) `R` is the order of `x` in the
[group of multiplicative units](ring-theory.groups-of-units-rings.md). In other
words, it is the [normal subgroup](group-theory.normal-subgroups.md) of the
[group of integers](elementary-number-theory.group-of-integers.md) consisting of
all [integers](elementary-number-theory.integers.md) `k` such that `xᵏ ＝ 1`.
