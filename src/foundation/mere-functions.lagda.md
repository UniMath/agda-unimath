# Mere functions

```agda
module foundation.mere-functions where
```

<details><summary>Imports</summary>

```agda
open import foundation.evaluation-functions
open import foundation.functoriality-propositional-truncation
open import foundation.propositional-truncations
open import foundation.universe-levels

open import foundation-core.function-types
open import foundation-core.propositions
```

</details>

## Idea

The type of
{{#concept "mere functions" Disambiguation="of types" Agda=mere-function}} from
`A` to `B` is the
[propositional truncation](foundation.propositional-truncations.md) of the type
of maps from `A` to `B`.

```text
  mere-function A B := ║(A → B)║₋₁
```

## Definitions

### Mere functions between types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  prop-mere-function : Prop (l1 ⊔ l2)
  prop-mere-function = trunc-Prop (A → B)

  mere-function : UU (l1 ⊔ l2)
  mere-function = type-Prop prop-mere-function

  is-prop-mere-function : is-prop mere-function
  is-prop-mere-function = is-prop-type-Prop prop-mere-function
```

### The evaluation map on mere functions

If we have a mere function from `A` to `B` and `A` is inhabited, then `B` is
inhabited.

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  ev-mere-function' : (mere-function A B) → A → ║ B ║₋₁
  ev-mere-function' |f| a = map-trunc-Prop (ev a) |f|

  ev-mere-function : (mere-function A B) → ║ A ║₋₁ → ║ B ║₋₁
  ev-mere-function |f| =
    rec-trunc-Prop (trunc-Prop B) (ev-mere-function' |f|)
```

### Mere functions form a reflexive relation

```agda
module _
  {l : Level} (A : UU l)
  where

  refl-mere-function : mere-function A A
  refl-mere-function = unit-trunc-Prop id
```

### Mere functions form a transitive relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  transitive-mere-function :
    mere-function B C → mere-function A B → mere-function A C
  transitive-mere-function =
    map-binary-trunc-Prop (λ g f → g ∘ f)
```

## See also

- [Mere logical equivalences](foundation.mere-logical-equivalences.md)
