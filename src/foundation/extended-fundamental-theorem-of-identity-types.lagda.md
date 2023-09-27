# The extended fundamental theorem of identity types

```agda
module foundation.extended-fundamental-theorem-of-identity-types where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

The **extended fundamental theorem of identity types** asserts that for any
[pointed](structured-types.pointed-types.md)
[connected type](foundation.connected-types.md) `A` equipped with a type family
`B` over `A`, i.e., for any [higher group](higher-group-theory.higher-groups.md)
`BG := A` equipped with a
[higher group action](higher-group-theory.higher-group-actions.md) `B` over `A`,
the following are equivalent:

1. Every family of maps
   ```text
     f : (x : A) → (* ＝ x) → B x
   ```
   is a family of `P`-maps.
2. The [total space](foundation.dependent-pair-types.md) `Σ A B` is
   [`P`-separated](foundation.separated-types.md).
