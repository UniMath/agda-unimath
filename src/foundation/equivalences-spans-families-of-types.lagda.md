# Equivalences of spans of families of types

```agda
module foundation.equivalences-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

An {{#concept "equivalence of spans on a family of types"}} from a
[span](foundation.spans-families-of-types.md) `s` on `A : I → 𝒰` to a span `t` on `A`
consists of an [equivalence](foundation-core.equivalences.md) `e : S ≃ T`
[equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the triangle

```text
      e
  S ----> T
   \     /
    \   /
     V V
      Aᵢ
```

[commutes](foundation.commuting-triangles-of-maps.md) for each `i : I`.

## See also

- [Equivalences of span diagrams on families of types](foundation.equivalences-span-diagrams-families-of-types.md)
