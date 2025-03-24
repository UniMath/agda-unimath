# Mere functions

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module foundation.mere-functions
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositional-truncations funext univalence
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
  ev-mere-function' |f| a =
    rec-trunc-Prop (trunc-Prop B) (λ f → unit-trunc-Prop (f a)) |f|

  ev-mere-function : (mere-function A B) → ║ A ║₋₁ → ║ B ║₋₁
  ev-mere-function |f| |a| =
    rec-trunc-Prop (trunc-Prop B) (ev-mere-function' |f|) (|a|)
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
  transitive-mere-function |g| =
    rec-trunc-Prop
      ( prop-mere-function A C)
      ( λ f →
        rec-trunc-Prop
          ( prop-mere-function A C)
          ( λ g → unit-trunc-Prop (g ∘ f))
          ( |g|))
```

## See also

- [Mere logical equivalences](foundation.mere-logical-equivalences.md)
