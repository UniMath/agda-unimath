# Subuniverse induction on modalities

```agda
module orthogonal-factorization-systems.subuniverse-induction-modalities where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

TODO

## Definition

Nonstandard terminology

```agda
ind-subuniverse-modality :
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○) →
  UU (lsuc l1 ⊔ l2)
ind-subuniverse-modality {l1} {l2} {○} unit-○ =
  (X : UU l1) (P : ○ X → UU l1) →
  (is-modal-family unit-○ P) →
  ((x : X) → P (unit-○ x)) →
  (x' : ○ X) → P x'

compute-ind-subuniverse-modality :
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○) →
  (ind-○ : ind-subuniverse-modality unit-○) →
  UU (lsuc l1 ⊔ l2)
compute-ind-subuniverse-modality {l1} {l2} {○} unit-○ ind-○ =
  (X : UU l1) (P : ○ X → UU l1) →
  (is-modal-P : is-modal-family unit-○ P) →
  (f : (x : X) → P (unit-○ x)) →
  (x : X) → ind-○ X P is-modal-P f (unit-○ x) ＝ f x
```

## Properties

### Subuniverse induction follows from modal induction

```agda
ind-subuniverse-ind-modality :
  {l : Level}
  {○ : operator-modality l l}
  (unit-○ : unit-modality ○) →
  ind-modality unit-○ → ind-subuniverse-modality unit-○
ind-subuniverse-ind-modality {○ = ○} unit-○ ind-○ X P is-modal-P f x' =
  map-retraction-is-equiv (is-modal-P x') (ind-○ X P (unit-○ ∘ f) x')

compute-ind-subuniverse-ind-modality :
  {l : Level}
  {○ : operator-modality l l}
  (unit-○ : unit-modality ○) →
  (ind-○ : ind-modality unit-○) →
  compute-ind-modality unit-○ ind-○ →
  compute-ind-subuniverse-modality unit-○
    ( ind-subuniverse-ind-modality unit-○ ind-○)
compute-ind-subuniverse-ind-modality
  unit-○ ind-○ compute-ind-○ X P is-modal-P f x =
  ( ap
    ( map-retraction-is-equiv (is-modal-P (unit-○ x)))
    ( compute-ind-○ X P (unit-○ ∘ f) x)) ∙
  ( is-section-is-equiv (is-modal-P (unit-○ x)) (f x))
```
