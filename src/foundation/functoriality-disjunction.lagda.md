# Functoriality of disjunction

```agda
module foundation.functoriality-disjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.disjunction
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels
```

</details>

## Idea

Any two implications `f : A ⇒ B` and `g : C ⇒ D` induce an implication
`map-disjunction f g : (A ∨ B) ⇒ (C ∨ D)`.

## Definitions

### The functorial action of disjunction

```agda
module _
  {l1 l2 l3 l4 : Level} (A : Prop l1) (B : Prop l2) (C : Prop l3) (D : Prop l4)
  (f : type-Prop (A ⇒ B)) (g : type-Prop (C ⇒ D))
  where

  map-disjunction : type-Prop ((A ∨ C) ⇒ (B ∨ D))
  map-disjunction =
    elim-disjunction (B ∨ D) (inl-disjunction ∘ f) (inr-disjunction ∘ g)
```
