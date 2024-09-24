# Globular homotopies

```agda
module structured-types.globular-homotopies where
```

<details><summary>Imports</summary>

```agda

```

</details>

## Idea

Consider two [globular maps](structured-types.globular-maps.md) `f g : G → H` into a [transitive globular type](structured-types.transitive-globular-types.md) `H`. There are two notions of globular homotopy between them, which aren't equivalent even though both generalize the notion of ordinary [homotopy](foundation-core.homotopies.md) in the case of viewing types as [globular types](structured-types.md) via the [identity type](foundation-core.identity-types.md).

### Standard globular homotopies

A {{#concept "standard globular homotopy"}} between `H : f ~ g` consists of

```text
  h₀ : {x y : G₀} → G' x y → H' (f₀ x) (g₀ y)
  h' : {x y : G₀} → h₀ x y ∘ f' x y ~ g' x y
```

where `f'` and `g'` are the globular maps between the [globular types](structured types.globular-types.md) `G' x y` and `H' (f₀ x) (f₀ y)`
