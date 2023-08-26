# Subuniverse induction

```agda
module orthogonal-factorization-systems.subuniverse-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.universe-levels

open import orthogonal-factorization-systems.induction-modalities
open import orthogonal-factorization-systems.modal-operators
```

</details>

## Idea

TODO

## Definition

Nonstandard terminology

### Subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  ind-subuniverse-modality =
    (X : UU l1) (P : ○ X → UU l1) → is-modal-family unit-○ P →
    ((x : X) → P (unit-○ x)) → (x' : ○ X) → P x'

  compute-ind-subuniverse-modality :
    ind-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-subuniverse-modality ind-○ =
    (X : UU l1) (P : ○ X → UU l1) (is-modal-P : is-modal-family unit-○ P) →
    (f : (x : X) → P (unit-○ x)) → (ind-○ X P is-modal-P f ∘ unit-○) ~ f
```

### Subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  rec-subuniverse-modality =
    (X Y : UU l1) → is-modal unit-○ Y →
    (X → Y) → ○ X → Y

  compute-rec-subuniverse-modality :
    rec-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-rec-subuniverse-modality rec-○ =
    (X Y : UU l1) (is-modal-Y : is-modal unit-○ Y) →
    (f : X → Y) → (rec-○ X Y is-modal-Y f ∘ unit-○) ~ f
```

### Strong subuniverse induction

We can weaken the assumption that the codomain is modal and only ask that the
unit has a retraction. We call this principle **strong subuniverse induction**.
Note that such a retraction may not in general be
[unique](foundation-core.contractible-types.md), and the computational behaviour
of this induction principle depends on the choice of retraction.

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-ind-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-ind-subuniverse-modality =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x' : ○ X) → retraction (unit-○ {P x'})) →
    ((x : X) → P (unit-○ x)) → (x' : ○ X) → P x'

  compute-strong-ind-subuniverse-modality :
    strong-ind-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-strong-ind-subuniverse-modality ind-○ =
    (X : UU l1) (P : ○ X → UU l1) →
    (is-premodal-P : (x' : ○ X) → retraction (unit-○ {P x'})) →
    (f : (x : X) → P (unit-○ x)) → (ind-○ X P is-premodal-P f ∘ unit-○) ~ f
```

### Strong subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-rec-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-rec-subuniverse-modality =
    (X Y : UU l1) → retraction (unit-○ {Y}) →
    (X → Y) → ○ X → Y

  compute-strong-rec-subuniverse-modality :
    strong-rec-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-strong-rec-subuniverse-modality rec-○ =
    (X Y : UU l1) (is-premodal-Y : retraction (unit-○ {Y})) →
    (f : X → Y) → (rec-○ X Y is-premodal-Y f ∘ unit-○) ~ f
```

## Properties

### Subuniverse recursion from subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-subuniverse-modality unit-○)
  where

  rec-subuniverse-ind-subuniverse-modality : rec-subuniverse-modality unit-○
  rec-subuniverse-ind-subuniverse-modality X Y is-modal-Y =
    ind-○ X (λ _ → Y) (λ _ → is-modal-Y)

  compute-rec-subuniverse-compute-ind-subuniverse-modality :
    (compute-ind-○ : compute-ind-subuniverse-modality unit-○ ind-○) →
    compute-rec-subuniverse-modality unit-○
      ( rec-subuniverse-ind-subuniverse-modality)
  compute-rec-subuniverse-compute-ind-subuniverse-modality
    compute-ind-○ X Y is-modal-Y =
      compute-ind-○ X (λ _ → Y) (λ _ → is-modal-Y)
```

### Subuniverse induction from strong subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : strong-ind-subuniverse-modality unit-○)
  where

  ind-subuniverse-strong-ind-subuniverse-modality :
    ind-subuniverse-modality unit-○
  ind-subuniverse-strong-ind-subuniverse-modality X P is-modal-P =
    ind-○ X P (retraction-is-equiv ∘ is-modal-P)

  compute-ind-subuniverse-strong-ind-subuniverse-modality :
    (compute-ind-○ : compute-strong-ind-subuniverse-modality unit-○ ind-○) →
    compute-ind-subuniverse-modality unit-○
      ( ind-subuniverse-strong-ind-subuniverse-modality)
  compute-ind-subuniverse-strong-ind-subuniverse-modality
    compute-ind-○ X P is-modal-P =
    compute-ind-○ X P (retraction-is-equiv ∘ is-modal-P)
```

### Subuniverse recursion from strong subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (rec-○ : strong-rec-subuniverse-modality unit-○)
  where

  rec-subuniverse-strong-rec-subuniverse-modality :
    rec-subuniverse-modality unit-○
  rec-subuniverse-strong-rec-subuniverse-modality X Y is-modal-Y =
    rec-○ X Y (retraction-is-equiv is-modal-Y)

  compute-rec-subuniverse-strong-rec-subuniverse-modality :
    (compute-rec-○ : compute-strong-rec-subuniverse-modality unit-○ rec-○) →
    compute-rec-subuniverse-modality unit-○
      ( rec-subuniverse-strong-rec-subuniverse-modality)
  compute-rec-subuniverse-strong-rec-subuniverse-modality
    compute-rec-○ X Y is-modal-Y =
    compute-rec-○ X Y (retraction-is-equiv is-modal-Y)
```

### Subuniverse induction from modal induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  where

  strong-ind-subuniverse-ind-modality : strong-ind-subuniverse-modality unit-○
  strong-ind-subuniverse-ind-modality X P is-premodal-P f x' =
    map-retraction unit-○ (is-premodal-P x') (ind-○ X P (unit-○ ∘ f) x')

  compute-strong-ind-subuniverse-ind-modality :
    compute-ind-modality unit-○ ind-○ →
    compute-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality)
  compute-strong-ind-subuniverse-ind-modality
    compute-ind-○ X P is-premodal-P f x =
    ( ap
      ( map-retraction unit-○ (is-premodal-P (unit-○ x)))
      ( compute-ind-○ X P (unit-○ ∘ f) x)) ∙
    ( is-retraction-map-retraction unit-○ (is-premodal-P (unit-○ x)) (f x))

  ind-subuniverse-ind-modality : ind-subuniverse-modality unit-○
  ind-subuniverse-ind-modality =
    ind-subuniverse-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality)

  compute-ind-subuniverse-ind-modality :
    compute-ind-modality unit-○ ind-○ →
    compute-ind-subuniverse-modality unit-○
      ( ind-subuniverse-ind-modality)
  compute-ind-subuniverse-ind-modality compute-ind-○ =
    compute-ind-subuniverse-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality)
      ( compute-strong-ind-subuniverse-ind-modality compute-ind-○)
```

### Subuniverse recursion from modal recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (rec-○ : rec-modality unit-○)
  where

  strong-rec-subuniverse-rec-modality : strong-rec-subuniverse-modality unit-○
  strong-rec-subuniverse-rec-modality X Y is-premodal-Y f x' =
    map-retraction unit-○ (is-premodal-Y) (rec-○ X Y (unit-○ ∘ f) x')

  compute-strong-rec-subuniverse-rec-modality :
    compute-rec-modality unit-○ rec-○ →
    compute-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality)
  compute-strong-rec-subuniverse-rec-modality
    compute-rec-○ X Y is-premodal-Y f x =
    ( ap
      ( map-retraction unit-○ (is-premodal-Y))
      ( compute-rec-○ X Y (unit-○ ∘ f) x)) ∙
    ( is-retraction-map-retraction unit-○ (is-premodal-Y) (f x))

  rec-subuniverse-rec-modality : rec-subuniverse-modality unit-○
  rec-subuniverse-rec-modality =
    rec-subuniverse-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality)

  compute-rec-subuniverse-rec-modality :
    compute-rec-modality unit-○ rec-○ →
    compute-rec-subuniverse-modality unit-○ (rec-subuniverse-rec-modality)
  compute-rec-subuniverse-rec-modality compute-rec-○ =
    compute-rec-subuniverse-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality)
      ( compute-strong-rec-subuniverse-rec-modality compute-rec-○)
```

## See also

- [Reflective subuniverses](orthogonal-factorization-systems.reflective-subuniverses.md)
