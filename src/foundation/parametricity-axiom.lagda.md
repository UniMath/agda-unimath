# The parametricity axiom

```agda
module foundation.parametricity-axiom where
```

<details><summary>Imports</summary>

```agda
open import foundation.axiom-of-choice
open import foundation.booleans
open import foundation.empty-types
open import foundation.law-of-excluded-middle
open import foundation.parametric-types
open import foundation.parametricity-booleans
open import foundation.universe-levels

open import foundation-core.negation
```

</details>

## Idea

The {{#concept "parametricity axiom" Agda=Parametricity}} states that all types
are [parametric](foundation.parametric-types.md). I.e., for each type `X : 𝒰`,
the [constant map](foundation.constant-maps.md)

```text
  X → (𝒰 → X)
```

is an [equivalence](foundation-core.equivalences.md).

## Definition

```agda
level-Parametricity : (l : Level) → UU (lsuc l)
level-Parametricity l = {X : UU l} → is-parametric l X

Parametricity : UUω
Parametricity = {l : Level} → level-Parametricity l
```

## Consequences

### Parametricity contradicts excluded middle

```agda
abstract
  no-LEM-level-Parametricity :
    {l : Level} → level-Parametricity l → ¬ level-LEM l
  no-LEM-level-Parametricity {l} H =
    no-LEM-is-parametric-bool
      ( is-parametric-equiv (compute-raise-bool l) (H {X = raise-bool l}))

  no-LEM-Parametricity : Parametricity → LEM → empty
  no-LEM-Parametricity H lem = no-LEM-level-Parametricity {lzero} H lem
```

### Parametricity contradicts the axiom of choice

```agda
abstract
  no-AC0-level-Parametricity :
    {l : Level} → level-Parametricity l → ¬ level-AC0 l l
  no-AC0-level-Parametricity {l} H =
    no-AC0-is-parametric-bool
      ( is-parametric-equiv (compute-raise-bool l) (H {X = raise-bool l}))

  no-AC0-Parametricity :
    Parametricity → AC0 → empty
  no-AC0-Parametricity H ac =
    no-AC0-level-Parametricity (H {l = lzero}) (ac {l1 = lzero} {l2 = lzero})
```

## References

{{#bibliography}} {{#reference Lord25}}
