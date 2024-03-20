# Deloopable H-spaces

```agda
module higher-group-theory.deloopable-h-spaces where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider an [H-space](structured-types.h-spaces.md) with underlying
[pointed type](structured-types.pointed-types.md) `(X , *)` and with
multiplication `μ` satisfying

```text
   left-unit-law : (x : X) → μ * x ＝ x
  right-unit-law : (x : X) → μ x * ＝ x
    coh-unit-law : left-unit-law * ＝ right-unit-law *.
```

A {{#concept "delooping" Disambiguation="H-space"}} of the H-space `X` consists
of an ∞-group `G` and an equivalence of H-spaces

```text
  X ≃ h-space-∞-Group G.
```
