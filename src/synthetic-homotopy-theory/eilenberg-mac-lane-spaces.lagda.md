# Eilenberg-Mac Lane spaces

```agda
module synthetic-homotopy-theory.eilenberg-mac-lane-spaces where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider a [group](group-theory.groups.md) `G` and a natural number `n ≥ 1`. We
will recursively define what it means for a
[pointed connected type](higher-group-theory.higher-groups.md) `X` to be an
$n$-th {{#concept "Eilenberg-Mac Lane space" Agda=is-eilenberg-mac-lane-space}}:

- We say that `X` is a **first Eilenberg-Mac Lane space** if there is a
  [pointed equivalence](structured-types.pointed-equivalences.md)

  ```text
    Ω X ≃ G
  ```

  that maps concatenation in the
  [loop space](synthetic-homotopy-theory.loop-spaces.md) `Ω X` to the group
  operation on `G`.

- We say that `X` is an $(n+1)$-st Eilenberg-Mac Lane space
