# Dependent products of subtypes

```agda
module foundation.dependent-products-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

Given an indexing type `I`, a type `Aᵢ` for each `i : I`, and a
[subtype](foundation.subtypes.md) `Sᵢ ⊆ Aᵢ` for each `i : I`, a function
`f : (i : I) → Aᵢ` is in the
{{#concept "dependent product" disambiguation="of subtypes" Agda=Π-subtype}} of
the subtypes `S` if for each `i`, `f i ∈ Sᵢ`.

## Definition

```agda
Π-subtype :
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} →
  ((i : I) → subtype l3 (A i)) →
  subtype (l1 ⊔ l3) ((i : I) → A i)
Π-subtype {I = I} S f = Π-Prop I (λ i → S i (f i))
```
