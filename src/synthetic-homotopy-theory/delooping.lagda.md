# Delooping

```agda
module synthetic-homotopy-theory.delooping where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider a [pointed type](structured-types.pointed types.md) `X` and a [pointed connected type](higher-group-theory.higher-groups.md) `Y`. We say that `Y` is a {{#concept "delooping" Agda=is-delooping}} of `X` if we have a [pointed equivalence](structured-types.pointed-equivalences.md)

```text
  X ≃∗ Ω Y.
```

Recall that a pointed connected type is
Similarly, we say that `X` is {{#concept "deloopable" Disambiguation="pointed type" Agda=is-deloopable}} in a universe `𝒰 l` if there is an element of type

```text
  is-deloopable X := Σ (Y : higher-group l), X ≃∗ Ω Y.
```
