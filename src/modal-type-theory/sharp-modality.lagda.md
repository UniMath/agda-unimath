# The sharp modality

```agda
{-# OPTIONS --cohesion --flat-split --rewriting #-}

module modal-type-theory.sharp-modality where

open import modal-type-theory.flat-modality

open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.higher-modalities
open import orthogonal-factorization-systems.modal-operators
open import orthogonal-factorization-systems.locally-small-modal-operators

open import foundation.universe-levels
open import foundation.dependent-pair-types
open import foundation.locally-small-types
open import foundation.action-on-identifications-functions
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.sections
open import foundation.equivalences
```

## Idea

TODO

## Definition

```agda
-- {-# BUILTIN REWRITE _＝_ #-}

postulate
  ♯ : {l : Level} (A : UU l) → UU l

  unit-♯ : {l : Level} {A : UU l} → A → ♯ A

  ind-♯ :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
    ((x : A) → ♯ (C (unit-♯ x))) →
    ((x : ♯ A) → ♯ (C x))

  compute-ind-♯ :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2)
    (f : (x : A) → ♯ (C (unit-♯ x))) →
    (ind-♯ C f ∘ unit-♯) ~ f

module _
  (l : Level)
  where

  ♯-locally-small-operator-modality : locally-small-operator-modality l l l
  pr1 ♯-locally-small-operator-modality = ♯ {l}
  pr2 ♯-locally-small-operator-modality A = is-locally-small' {l} {♯ A}

  dependent-universal-property-modality-♯ :
    dependent-universal-property-modality {l} unit-♯
  pr1 dependent-universal-property-modality-♯ X = ind-♯
  pr2 dependent-universal-property-modality-♯ X = compute-ind-♯
```

### Sharp recursion

```agda
rec-♯ :
    {l1 l2 : Level} {A : UU l1} (B : UU l2) →
    (A → ♯ B) → (♯ A → ♯ B)
rec-♯ B = ind-♯ (λ _ → B)

compute-rec-♯ :
    {l1 l2 : Level} {A : UU l1} (B : UU l2)
    (f : A → ♯ B) →
    (rec-♯ B f ∘ unit-♯) ~ f
compute-rec-♯ B = compute-ind-♯ (λ _ → B)
```

### Action on maps

```agda
ap-♯ : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → (♯ A → ♯ B)
ap-♯ {B = B} f = rec-♯ B (unit-♯ ∘ f)

-- {-# REWRITE compute-ind-♯ #-}

-- judgemental version of "induced map ♭ A → ♭ (♯ A) is an equivalence"
postulate
  crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A
  compute-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) → (crisp-elim-♯ (unit-♯ x)) ＝ x
  uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : ♯ A) → unit-♯ (crisp-elim-♯ x) ＝ x

-- {-# REWRITE compute-crisp-elim-♯ #-}

postulate
  -- coherence between computation and uniqueness rules for `crisp-elim-♯`
  coherence-uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    uniqueness-crisp-elim-♯ (unit-♯ x) ＝ ap unit-♯ (compute-crisp-elim-♯ x)
```

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
