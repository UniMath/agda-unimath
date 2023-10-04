# Morphisms of types equipped with automorphisms

```agda
module structured-types.morphisms-types-equipped-with-automorphisms
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider two
[types equipped with an automorphism](structured-types.types-equipped-with-automorphisms.md)
`(X,e)` and `(Y,f)`. A **morphism** from `(X,e)` to `(Y,f)` consists of a map
`h : X → Y` equipped with a [homotopy](foundation-core.homotopies.md) witnessing
that the square

```text
      h
  X -----> Y
  |        |
 e|        |f
  V        V
  X -----> Y
      h
```

[commutes](foundation.commuting-squares-of-maps.md).
