# Cartesian dependent span diagrams

```agda
module foundation.cartesian-dependent-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-span-diagrams
open import foundation.dependent-span-diagrams
open import foundation.span-diagrams
open import foundation.universe-levels
```

</details>

## Idea

A [dependent span diagram](foundation.dependent-span-diagrams.md) `𝒯` over a [span diagram](foundation.span-diagrams.md) `𝒮 := (A <-f- S -g-> B)` is said to be {{#concept "cartesian" Disambiguation="dependent span diagram (condition)"}} if the maps

```text
  𝒯₂ s → 𝒯₀ (f s)
  𝒯₂ s → 𝒯₁ (g s)
```

are [equivalences](foundation-core.equivalences.md) for each `s : S`. In other
words, a dependent span diagram `𝒯` over `𝒮` is cartesian if the display span
diagram `𝒯 s` is [constant](foundation.constant-span-diagrams.md) for every
`s : S`.

The condition of being a cartesian dependent span diagram is equivalent to the condition that the [flattening](foundation.flattening-dependent-span-diagrams.md)

```text
  Σ (a : A), 𝒯₀ a <----- Σ (s : S), 𝒯₂ s -----> Σ (b : B), 𝒯₁ b
         |                       |                       |
         |                       |                       |
         ∨                       ∨                       ∨
         A <-------------------- S --------------------> B
```

of `𝒯` is a [cartesian morphism](foundation.cartesian-morphisms-span-diagrams.md)

Notice that in the definition of cartesian dependent span diagrams, the type of type families `𝒯₂` over the spanning type `S` of `𝒮` equipped with a family of equivalences `𝒯₂ s ≃ P (f s)` is [contractible](foundation-core.contractible-types.md). Therefore we define a {{#concept "cartesian dependent span diagram"}} over `𝒮` more succinctly to consist of

```text
  P : A → 𝒰
  Q : B → 𝒰
  e : (s : S) → P (f s) ≃ Q (g s).
```

We will show that the type of cartesian dependent span diagrams over `𝒮` is equivalent to the type of base changes of `𝒮`.

## Definitions

### The predicate of being a cartesian dependent span diagram

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : span-diagram l1 l2 l3) (𝒯 : dependent-span-diagram l4 l5 l6 𝒮)
  where

  is-cartesian-dependent-span-diagram : UU (l3 ⊔ l4 ⊔ l5 ⊔ l6)
  is-cartesian-dependent-span-diagram =
    (s : spanning-type-span-diagram 𝒮) →
    is-constant-span-diagram (display-dependent-span-diagram 𝒯 s)
```
