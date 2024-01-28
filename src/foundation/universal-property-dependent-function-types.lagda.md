# The universal property of dependent function types

```agda
module foundation.universal-property-dependent-function-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.spans-families-of-types
open import foundation.terminal-spans-families-of-types
open import foundation.universe-levels
```

</details>

## Idea

Consider a family of types `B` over `A`. Then the dependent function type `(a : A) → B a` naturally has the structure of a [span](foundation.spans-families-of-types.md) on the family of types `B` over `A`, where for each `a : A` the map

```text
  ((x : A) → B x) → B a
```

is given by evaluation at `a`.

A span `𝒮 := (S , f)` is said to satisfy the {{#concept "universal property of dependent function types" Agda=universal-property-dependent-function-types}} if for any type `T` the map

```text
  (T → S) → ((x : A) → T → B x)
```

given by `h ↦ λ x t → f x (h t)` is an [equivalence](foundation-core.equivalences.md). The dependent function type `(x : A) → B x` equipped with the span structure defined above satisfies the universal property of dependent function types.

The universal property of dependent function types is also shown to be equivalent to being a [terminal span](foundation.terminal-spans-families-of-types.md) on the type family `B`.

## Definitions

### The universal property of dependent function types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (𝒮 : span-family-of-types l3 B)
  where

  ev-span-family-of-types :
    {l : Level} (T : UU l) →
    (T → spanning-type-span-family-of-types 𝒮) → (x : A) → T → B x
  ev-span-family-of-types T h x t = map-span-family-of-types 𝒮 x (h t)

  universal-property-dependent-function-types : UUω
  universal-property-dependent-function-types =
    {l : Level} (T : UU l) → is-equiv (ev-span-family-of-types T)
```

## Properties

### A span on a family of types satisfies the universal property of dependent function types if and only if it is terminal

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} (𝒮 : span-family-of-types l3 B)
  where

  abstract
    is-terminal-universal-property-dependent-function-types :
      universal-property-dependent-function-types 𝒮 →
      is-terminal-span-family-of-types 𝒮
    is-terminal-universal-property-dependent-function-types U 𝒯 =
      is-contr-equiv' _
        ( equiv-tot
          ( λ h →
            ( equiv-Π-equiv-family
              ( λ a →
                ( equiv-Π-equiv-family (λ t → equiv-inv _ _)) ∘e
                ( equiv-funext))) ∘e
            ( equiv-funext)))
        ( is-contr-map-is-equiv
          ( U (spanning-type-span-family-of-types 𝒯))
          ( map-span-family-of-types 𝒯))

  abstract
    universal-property-dependent-function-types-is-terminal :
      is-terminal-span-family-of-types 𝒮 →
      universal-property-dependent-function-types 𝒮
    universal-property-dependent-function-types-is-terminal U T =
      is-equiv-is-contr-map
        ( λ g →
          is-contr-equiv _
            ( equiv-tot
              ( λ h →
                ( equiv-Π-equiv-family
                  ( λ a →
                    ( equiv-Π-equiv-family (λ t → equiv-inv _ _)) ∘e
                    ( equiv-funext))) ∘e
                ( equiv-funext)))
            ( U (T , g)))
```
