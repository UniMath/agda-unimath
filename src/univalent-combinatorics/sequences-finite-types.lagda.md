# Sequences of elements in finite types

```agda
module univalent-combinatorics.sequences-finite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.functions
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.pairs-of-distinct-elements
open import foundation.repetitions
open import foundation.repetitions-sequences
open import foundation.sequences

open import univalent-combinatorics.pigeonhole-principle
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Sequences of elements in finite types must have repetitions. Furthermore, since equality in finite types is decidable, there must be a first repetition in any sequence of elements in a finite type.

## Properties

```agda
repetition-sequence-Fin :
  (k : ℕ) (f : sequence (Fin k)) → repetition-sequence f
repetition-sequence-Fin k f =
  map-emb-repetition
    ( f ∘ nat-Fin (succ-ℕ k))
    ( f)
    ( emb-nat-Fin (succ-ℕ k))
    ( id-emb)
    ( refl-htpy)
    ( repetition-le-Fin (succ-ℕ k) k (f ∘ nat-Fin (succ-ℕ k)) (le-succ-ℕ {k}))

pair-of-distinct-elements-repetition-sequence-Fin :
  {k : ℕ} (f : sequence (Fin k)) → pair-of-distinct-elements ℕ
pair-of-distinct-elements-repetition-sequence-Fin {k} f =
  pair-of-distinct-elements-repetition f (repetition-sequence-Fin k f)

fst-repetition-sequence-Fin :
  {k : ℕ} (f : sequence (Fin k)) → ℕ
fst-repetition-sequence-Fin {k} f =
  fst-repetition f (repetition-sequence-Fin k f)

snd-repetition-sequence-Fin :
  {k : ℕ} (f : sequence (Fin k)) → ℕ
snd-repetition-sequence-Fin {k} f =
  snd-repetition f (repetition-sequence-Fin k f)

distinction-repetition-sequence-Fin :
  {k : ℕ} (f : sequence (Fin k)) →
  ¬ (Id (fst-repetition-sequence-Fin f) (snd-repetition-sequence-Fin f))
distinction-repetition-sequence-Fin {k} f =
  distinction-repetition f (repetition-sequence-Fin k f)

is-repetition-pair-of-distinct-elements-repetition-sequence-Fin :
  {k : ℕ} (f : sequence (Fin k)) →
  is-repetition-pair-of-distinct-elements f
    ( pair-of-distinct-elements-repetition-sequence-Fin f)
is-repetition-pair-of-distinct-elements-repetition-sequence-Fin {k} f =
  is-repetition-pair-of-distinct-elements-repetition f
    ( repetition-sequence-Fin k f)

le-fst-repetition-sequence-Fin :
  {k : ℕ} (f : sequence (Fin k)) →
  le-ℕ (fst-repetition-sequence-Fin f) (succ-ℕ k)
le-fst-repetition-sequence-Fin {k} f =
  strict-upper-bound-nat-Fin
    ( succ-ℕ k)
    ( pr1
      ( pr1
        ( repetition-le-Fin (succ-ℕ k) k (f ∘ nat-Fin (succ-ℕ k)) (le-succ-ℕ {k}))))
```
