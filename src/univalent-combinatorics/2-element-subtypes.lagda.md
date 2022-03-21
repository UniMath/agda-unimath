# 2-element subtypes

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.2-element-subtypes where

open import foundation.coproduct-types using (coprod; inl; inr)
open import foundation.decidable-types using (is-decidable)
open import foundation.decidable-propositions using
  ( decidable-Prop; is-decidable-type-decidable-Prop; is-prop-type-decidable-Prop; type-decidable-Prop)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using (_≃_)
open import foundation.identity-types using (Id)
open import foundation.unit-type using (star)
open import foundation.universe-levels using (Level; UU; lzero; lsuc; _⊔_)

open import univalent-combinatorics.finite-types using (has-cardinality)
open import univalent-combinatorics.standard-finite-types using (Fin)
```

## Idea

...

## Definition

```agda
module _
  {l1 l2 : Level} (X : UU l1)
  where

  2-Element-Subtype : UU (l1 ⊔ lsuc l2)
  2-Element-Subtype =
    Σ (X → decidable-Prop l2) λ P → has-cardinality 2 (Σ X (λ x → type-decidable-Prop (P x)))

{-
  D : UU (l1 ⊔ lsuc l2)
  D = ((pair P H) : 2-Element-Subtype) → Σ X (λ x → type-decidable-Prop (P x))

  phi : D → D → Fin 2
  phi d d' = {!!}
    where
    phi-ev : (Y : 2-Element-Subtype) → is-decidable (Id (d Y) (d' Y)) → Fin 2
    phi-ev Y (inl p) = inl (inr star)
    phi-ev Y (inr np) = inr star
-}

  
```
