# Equivalences

```agda
{-# OPTIONS --without-K --exact-split #-}

module univalent-combinatorics.equivalences where

open import foundation.equivalences public

open import foundation.decidable-types using
  ( is-decidable; is-decidable-iff; is-decidable-prod)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU)

open import univalent-combinatorics.embeddings using
  ( is-decidable-is-emb-is-finite)
open import univalent-combinatorics.finite-types using (is-finite)
open import univalent-combinatorics.surjective-maps using
  ( is-equiv-is-emb-is-surjective; is-surjective-is-equiv;
    is-decidable-is-surjective-is-finite)
```

## Properties

### For a map between finite types, being an equivalence is decidable

```agda
is-decidable-is-equiv-is-finite :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-finite A → is-finite B → is-decidable (is-equiv f)
is-decidable-is-equiv-is-finite f HA HB =
  is-decidable-iff
    ( λ p → is-equiv-is-emb-is-surjective (pr1 p) (pr2 p))
    ( λ K → pair (is-surjective-is-equiv K) (is-emb-is-equiv K))
    ( is-decidable-prod
      ( is-decidable-is-surjective-is-finite f HA HB)
      ( is-decidable-is-emb-is-finite f HA HB))
```
