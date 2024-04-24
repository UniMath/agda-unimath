# Null families of types

```agda
module orthogonal-factorization-systems.null-families-of-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.null-types
open import orthogonal-factorization-systems.orthogonal-maps
```

</details>

## Idea

A family of types `B : A → UU l` is said to be
{{#concept "null" Disambiguation="family of types" Agda=is-null-family}} at `Y`,
or **`Y`-null**, if every [fiber](foundation-core.fibers-of-maps.md) is. I.e.,
if the [diagonal map](foundation.diagonal-maps-of-types.md)

```text
  Δ : B x → (Y → B x)
```

is an [equivalence](foundation-core.equivalences.md) for every `x` in `A`.

## Definitions

### `Y`-null families of types

```agda
module _
  {l1 l2 l3 : Level} (Y : UU l1) {A : UU l2} (B : A → UU l3)
  where

  is-null-family : UU (l1 ⊔ l2 ⊔ l3)
  is-null-family = (x : A) → is-null Y (B x)

  is-property-is-null-family : is-prop is-null-family
  is-property-is-null-family =
    is-prop-Π (λ x → is-prop-is-null Y (B x))

  is-null-family-Prop : Prop (l1 ⊔ l2 ⊔ l3)
  pr1 is-null-family-Prop = is-null-family
  pr2 is-null-family-Prop = is-property-is-null-family
```

## See also

- [Null maps](orthogonal-factorization-systems.null-maps.md)
