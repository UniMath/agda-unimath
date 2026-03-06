# The parametricity axiom

```agda
module foundation.parametricity-axiom where
```

<details><summary>Imports</summary>

```agda
open import foundation.parametric-types
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "parametricity axiom" Agda=Parametricity}} states that all types
are [parametric](foundation.parametric-types.md) at their own
[universe level](foundation.universe-levels.md). I.e., for each type `X : 𝒰`,
the [constant map](foundation.constant-maps.md)

```text
  X → (𝒰 → X)
```

is an [equivalence](foundation-core.equivalences.md).

Jem Lord {{#cite Lord25}} presents this as _internal parametricity_. Since we
only work internally to type theory internal parametricity is all we can reason
about, so we dub it simply _parametricity_. Many consequences of parametricity
are also explored in {{#cite BELS17}}.

## Definition

```agda
level-Parametricity : (l : Level) → UU (lsuc l)
level-Parametricity l = {X : UU l} → is-parametric l X

Parametricity : UUω
Parametricity = {l : Level} → level-Parametricity l
```

## References

{{#bibliography}}
