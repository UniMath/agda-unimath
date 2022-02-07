# Propositional maps

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.propositional-maps where

open import foundation.contractible-types using (is-contr-equiv; is-contr)
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.embeddings using (is-emb; _↪_; map-emb; is-emb-map-emb)
open import foundation.equivalences using (is-equiv-comp'; _≃_)
open import foundation.fibers-of-maps using (fib)
open import foundation.functions using (_∘_)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id; fundamental-theorem-id')
open import foundation.identity-types using
  ( Id; refl; ap; inv; equiv-inv; is-equiv-inv)
open import foundation.propositions using
  ( is-prop; is-proof-irrelevant-is-prop; is-prop-is-proof-irrelevant; UU-Prop)
open import foundation.universe-levels using (Level; UU; _⊔_)
```

## Idea

A map is said to be propositional if its fibers are propositions. This condition is equivalent to being an embedding.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-prop-map : (A → B) → UU (l1 ⊔ l2)
  is-prop-map f = (b : B) → is-prop (fib f b)
```

## Properties

### The fibers of a map are propositions if and only if it is an embedding

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  abstract
    is-emb-is-prop-map : is-prop-map f → is-emb f
    is-emb-is-prop-map is-prop-map-f x =
      fundamental-theorem-id x refl
        ( is-contr-equiv
          ( fib f (f x))
          ( equiv-tot (λ y → equiv-inv (f x) (f y)))
          ( is-proof-irrelevant-is-prop (is-prop-map-f (f x)) (pair x refl)))
        ( λ y → ap f)

  abstract
    is-prop-map-is-emb : is-emb f → is-prop-map f
    is-prop-map-is-emb is-emb-f y =
      is-prop-is-proof-irrelevant α
      where
      α : (t : fib f y) → is-contr (fib f y)
      α (pair x refl) =
        fundamental-theorem-id' x refl
          ( λ y → inv ∘ ap f)
          ( λ y →
            is-equiv-comp' inv (ap f)
              ( is-emb-f x y)
              ( is-equiv-inv (f x) (f y)))

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-prop-map-emb : (f : B ↪ A) → is-prop-map (map-emb f)
    is-prop-map-emb f = is-prop-map-is-emb (is-emb-map-emb f)

  fib-emb-Prop : A ↪ B → B → UU-Prop (l1 ⊔ l2)
  pr1 (fib-emb-Prop f y) = fib (map-emb f) y
  pr2 (fib-emb-Prop f y) = is-prop-map-is-emb (is-emb-map-emb f) y
```
