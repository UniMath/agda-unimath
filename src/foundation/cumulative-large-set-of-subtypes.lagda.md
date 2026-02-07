# The cumulative large set of subtypes

```agda
module foundation.cumulative-large-set-of-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cumulative-large-set-of-propositions
```

</details>

## Idea

## Definition

```agda
raise-subtype :
  (l : Level) →
  {l1 l2 : Level} →
  {A : UU l1} →
  subtype l2 A →
  subtype (l2 ⊔ l) A
raise-subtype l B x = raise-Prop l (B x)

compute-raise-subtype :
  (l : Level) → {l1 l2 : Level} → {A : UU l1} →
  (S : subtype l2 A) → type-subtype S ≃ type-subtype (raise-subtype l S)
compute-raise-subtype l S = equiv-tot (compute-raise l ∘ type-Prop ∘ S)
```
