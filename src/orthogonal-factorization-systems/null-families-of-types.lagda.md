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
open import foundation.retracts-of-types
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
  is-null-family-Prop = (is-null-family , is-property-is-null-family)
```

## Properties

### Nullity is closed under equivalences

```agda
module _
  {l1 l2 l3 l4 : Level} {X : UU l1} {Y : UU l2} {A : UU l3} {B : A → UU l4}
  where

  is-null-family-equiv :
    {l5 : Level} {C : A → UU l5} →
    X ≃ Y → ((x : A) → C x ≃ B x) →
    is-null-family Y B → is-null-family X C
  is-null-family-equiv e f H x = is-null-equiv e (f x) (H x)

  is-null-family-equiv-exponent :
    (e : X ≃ Y) → is-null-family Y B → is-null-family X B
  is-null-family-equiv-exponent e H x = is-null-equiv-exponent e (H x)

module _
  {l1 l2 l3 l4 : Level} {Y : UU l1} {A : UU l2} {B : A → UU l3} {C : A → UU l4}
  where

  is-null-family-equiv-family :
    ((x : A) → C x ≃ B x) → is-null-family Y B → is-null-family Y C
  is-null-family-equiv-family f H x = is-null-equiv-base (f x) (H x)
```

### Retracts of `Y`-null families are `Y`-null

```agda
module _
  {l1 l2 l3 l4 : Level} {Y : UU l1} {A : UU l2} {B : A → UU l3} {C : A → UU l4}
  where

  is-null-family-retract :
    ((x : A) → (C x) retract-of (B x)) → is-null-family Y B → is-null-family Y C
  is-null-family-retract f H x = is-null-retract (f x) (H x)
```

## See also

- In [`null-maps`](orthogonal-factorization-systems.null-maps.md) we show that a
  type family is `Y`-null if and only if its total space projection is.
