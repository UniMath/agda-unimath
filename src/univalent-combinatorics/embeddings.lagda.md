# Injective maps

```agda
module univalent-combinatorics.embeddings where

open import foundation.embeddings public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.coproduct-types
open import foundation.decidable-embeddings
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.injective-maps
open import univalent-combinatorics.retracts-of-finite-types
```

</details>

## Idea

Embeddings in the presence of finite types enjoy further properties.

## Properties

```agda
is-decidable-is-emb-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-emb f)
is-decidable-is-emb-is-finite f HA HB =
  is-decidable-iff
    ( is-emb-is-injective (is-set-is-finite HB))
    ( is-injective-is-emb)
    ( is-decidable-is-injective-is-finite f HA HB)
```

### If `A` can be count, then `trunc-Prop A ↪ᵈ A`

```agda
decidable-emb-trunc-Prop-count :
  {l : Level} {A : UU l} →
  count A → type-trunc-Prop (A) ↪ᵈ A
decidable-emb-trunc-Prop-count (zero-ℕ , empty-A) =
  decidable-emb-is-empty (is-empty-type-trunc-Prop ( map-inv-equiv empty-A))
decidable-emb-trunc-Prop-count {A = A} (succ-ℕ n , e) =
  decidable-emb-retract-count
    ( succ-ℕ n , e)
    ( λ _ → map-equiv e (inr star))
    ((λ x → unit-trunc-Prop x) , (λ x → eq-is-prop is-prop-type-trunc-Prop))

module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  decidable-emb-tot-trunc-Prop-count :
    ((a : A) → count (P a)) → (Σ A (λ a → type-trunc-Prop (P a)) ↪ᵈ Σ A P)
  decidable-emb-tot-trunc-Prop-count c =
    decidable-emb-tot ( λ a → decidable-emb-trunc-Prop-count (c a))
```
