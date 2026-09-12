# Central H-spaces

```agda
module structured-types.central-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.equivalences
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

In [`structured-types.h-spaces`](structured-types.h-spaces.md) we saw that the
type of H-space structures on a
[pointed type](structured-types.pointed-types.md) `A` is equivalently described
as the type of [pointed sections](structured-types.pointed-types.md) of the
pointed evaluation map `(A → A) →∗ A`. If the type `A` is
[connected](foundation.connected-types.md), then the section maps to the
[connected component](foundation.connected-components.md) of `(A ≃ A)` at the
identity [equivalence](foundation-core.equivalences.md). An
{{#concept "evaluative H-space" Agda=is-central-h-space}} is a pointed type such
that the map `ev_pt : (A ≃ A)_(id) → A` is an equivalence.

## Definition

```agda
is-central-h-space :
  {l : Level} (A : Pointed-Type l) → UU l
is-central-h-space A =
  is-equiv
    { A = type-Pointed-Type A → type-Pointed-Type A}
    ( ev-point-Pointed-Type A)
```

## References

{{#bibliography}} {{#reference BCFR23}}
