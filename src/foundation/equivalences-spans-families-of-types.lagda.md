# Equivalences of spans of families of types

```agda
module foundation.equivalences-spans-families-of-types where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

We consider two concepts of equivalences between spans, according to the two
different concepts of spans of families of types:

- Equivalences of spans of a fixed family of types.
- Equivalences of spans of families of types indexed by a fixed indexing type.

### Equivalences of spans of fixed families of types

A **equivalence of spans of a fixed family of types** from a
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

### Equivalences of span of families of types

A **equivalence of spans** from a [span](foundation.spans-families-of-types.md) `(A , s)` of families of types indexed by a type `I`
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

### Equivalences of spans of families of types

The notion of **equivalence of spans of (fixed) families of types** is the
natural generalization of the notion of equivalences of (fixed) families of
types.


