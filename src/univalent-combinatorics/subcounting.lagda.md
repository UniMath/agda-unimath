# Subcounting

```agda
module univalent-combinatorics.subcounting where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.embeddings
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-propositional-truncation
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import univalent-combinatorics.counting
open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A {{#concept "subcounting" Agda=subcount}} of a type `X` is an
[embedding](foundation-core.embeddings.md) of `X` into a
[standard finite type](univalent-combinatorics.standard-finite-types.md).

## Definitions

```agda
subcount : {l : Level} → UU l → UU l
subcount X = Σ ℕ (λ k → X ↪ Fin k)

module _
  {l : Level} {X : UU l} (e : subcount X)
  where

  bound-number-of-elements-subcount : ℕ
  bound-number-of-elements-subcount = pr1 e

  emb-subcount : X ↪ Fin bound-number-of-elements-subcount
  emb-subcount = pr2 e

  map-subcount : X → Fin bound-number-of-elements-subcount
  map-subcount = map-emb emb-subcount

  is-set-has-subcount : is-set X
  is-set-has-subcount =
    is-set-emb emb-subcount (is-set-Fin bound-number-of-elements-subcount)

  has-decidable-equality-has-subcount : has-decidable-equality X
  has-decidable-equality-has-subcount =
    has-decidable-equality-emb emb-subcount
      ( has-decidable-equality-Fin bound-number-of-elements-subcount)
```

## Properties

### The elements of the standard finite types can be subcounted

```agda
subcount-Fin : (k : ℕ) → subcount (Fin k)
pr1 (subcount-Fin k) = k
pr2 (subcount-Fin k) = id-emb
```

### A counting is a subcounting

```agda
subcount-count : {l : Level} {X : UU l} → count X → subcount X
subcount-count (n , e) = (n , emb-equiv (inv-equiv e))
```

### Types equipped with subcountings are closed under subtypes

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  abstract
    emb-subcount-emb :
      (Y ↪ X) → (f : subcount X) → Y ↪ Fin (bound-number-of-elements-subcount f)
    emb-subcount-emb e f = comp-emb (emb-subcount f) e

  subcount-emb : (Y ↪ X) → subcount X → subcount Y
  pr1 (subcount-emb e f) = bound-number-of-elements-subcount f
  pr2 (subcount-emb e f) = emb-subcount-emb e f

  subcount-is-emb : {f : Y → X} → is-emb f → subcount X → subcount Y
  subcount-is-emb H = subcount-emb (_ , H)
```

### A type has sub-0 elements if and only if it is empty

```agda
abstract
  is-empty-is-zero-bound-number-of-elements-subcount :
    {l : Level} {X : UU l} (e : subcount X) →
    is-zero-ℕ (bound-number-of-elements-subcount e) → is-empty X
  is-empty-is-zero-bound-number-of-elements-subcount (.0 , e) refl = map-emb e
```

### If the elements of a type can be subcounted, then the elements of its propositional truncation can be subcounted

**Proof.** Given a subcounting `X ↪ Fin k`, then, by the functorial action of
propositional truncations, we have an embedding `║X║₋₁ ↪ ║Fin k║₋₁`. By
induction, if `k ≐ 0` then `║Fin k║₋₁ ≃ 0 ≃ Fin 0` and so `║X║₋₁ ↪ Fin 0` is a
subcounting. Otherwise, if `k ≐ j + 1`, then `║Fin k║₋₁ ≃ 1 ≃ Fin 1` and again
`║X║₋₁ ↪ Fin 1` is a subcounting.

```agda
module _
  {l : Level} {X : UU l}
  where

  subcount-trunc-Prop : subcount X → subcount ║ X ║₋₁
  subcount-trunc-Prop (0 , f , is-emb-f) =
    ( 0 ,
      rec-trunc-Prop empty-Prop id ∘ map-trunc-Prop f ,
      is-emb-is-prop is-prop-type-trunc-Prop is-prop-empty)
  subcount-trunc-Prop (succ-ℕ k , f , is-emb-f) =
    ( 1 ,
      rec-trunc-Prop Fin-1-Prop (λ _ → inr star) ∘ map-trunc-Prop f ,
      is-emb-is-prop is-prop-type-trunc-Prop is-prop-Fin-1)
```
