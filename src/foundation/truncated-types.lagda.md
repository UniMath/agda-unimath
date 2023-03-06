# Truncated types

<details><summary>Imports</summary>
```agda
module foundation.truncated-types where
open import foundation-core.truncated-types public
open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.embeddings
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.truncation-levels
open import foundation-core.univalence
open import foundation-core.universe-levels
open import foundation.subtype-identity-principle
open import foundation.univalence
```
</details>

## Definition

### The subuniverse of truncated types is itself truncated

```agda
is-contr-total-equiv-Truncated-Type :
  {l : Level} {k : 𝕋} (A : Truncated-Type l k) →
  is-contr (Σ (Truncated-Type l k) (type-equiv-Truncated-Type A))
is-contr-total-equiv-Truncated-Type A =
  is-contr-total-Eq-subtype
    ( is-contr-total-equiv (type-Truncated-Type A))
    ( is-prop-is-trunc _)
    ( type-Truncated-Type A)
    ( id-equiv)
    ( is-trunc-type-Truncated-Type A)

extensionality-Truncated-Type :
  {l : Level} {k : 𝕋} (A B : Truncated-Type l k) →
  (A ＝ B) ≃ type-equiv-Truncated-Type A B
extensionality-Truncated-Type A =
  extensionality-type-subtype
    ( is-trunc-Prop _)
    ( is-trunc-type-Truncated-Type A)
    ( id-equiv)
    ( λ X → equiv-univalence)

abstract
  is-trunc-Truncated-Type :
    {l : Level} (k : 𝕋) → is-trunc (succ-𝕋 k) (Truncated-Type l k)
  is-trunc-Truncated-Type k X Y =
    is-trunc-equiv k
      ( type-equiv-Truncated-Type X Y)
      ( extensionality-Truncated-Type X Y)
      ( is-trunc-type-equiv-Truncated-Type X Y)

Truncated-Type-Truncated-Type :
  (l : Level) (k : 𝕋) → Truncated-Type (lsuc l) (succ-𝕋 k)
pr1 (Truncated-Type-Truncated-Type l k) = Truncated-Type l k
pr2 (Truncated-Type-Truncated-Type l k) = is-trunc-Truncated-Type k
```

### The embedding of the subuniverse of truncated types into the universe

```agda
emb-type-Truncated-Type : (l : Level) (k : 𝕋) → Truncated-Type l k ↪ UU l
emb-type-Truncated-Type l k = emb-subtype (is-trunc-Prop k)
```
