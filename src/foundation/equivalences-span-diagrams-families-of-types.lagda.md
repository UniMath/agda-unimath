# Equivalences of span diagrams on families of types

```agda
module foundation.equivalences-span-diagrams-families-of-types where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

An {{#concept "equivalence of span diagrams on families of types"}} from a [span](foundation.spans-families-of-types.md) `(A , s)` of families of types indexed by a type `I`
to a span `(B , t)` indexed by `I` consists of a [family of equivalences](foundation-core.families-of-equivalences.md) `h : Aᵢ ≃ Bᵢ`, and an equivalence `e : S ≃ T` [equipped](foundation.structure.md) with a family of
[homotopies](foundation-core.homotopies.md) witnessing that the square

```text
         e
     S -----> T
     |        |
  fᵢ |        | gᵢ
     V        V
     Aᵢ ----> Bᵢ
         h
```

[commutes](foundation-core.commuting-squares-of-maps.md) for each `i : I`.


## See also

- [Equivalences of spans on families of types](foundation.equivalences-spans-families-of-types.md)
