# Subuniverse induction

```agda
module orthogonal-factorization-systems.subuniverse-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections-of-maps-of-maps
open import foundation.type-theoretic-principle-of-choice
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

  induction-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  induction-principle-subuniverse-modality =
    (X : UU l1) (P : ○ X → UU l1) (is-modal-P : is-modal-family unit-○ P) →
    section-Π (precomp-Π unit-○ P)

  ind-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  ind-subuniverse-modality =
    (X : UU l1) (P : ○ X → UU l1) → is-modal-family unit-○ P →
    ((x : X) → P (unit-○ x)) → (x' : ○ X) → P x'

  compute-ind-subuniverse-modality :
    ind-subuniverse-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-subuniverse-modality ind-○ =
    (X : UU l1) (P : ○ X → UU l1) (is-modal-P : is-modal-family unit-○ P) →
    (f : (x : X) → P (unit-○ x)) → (ind-○ X P is-modal-P f ∘ unit-○) ~ f

  ind-induction-principle-subuniverse-modality :
    induction-principle-subuniverse-modality → ind-subuniverse-modality
  ind-induction-principle-subuniverse-modality I X P is-modal-P =
    map-section-Π (precomp-Π unit-○ P) (I X P is-modal-P)
```

### Subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  recursion-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  recursion-principle-subuniverse-modality =
    (X Y : UU l1) → is-modal unit-○ Y → section-Π (precomp {A = X} unit-○ Y)

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

  strong-induction-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-induction-principle-subuniverse-modality =
    (X : UU l1) (P : ○ X → UU l1) →
    ((x' : ○ X) → retraction (unit-○ {P x'})) →
    section-Π (precomp-Π unit-○ P)

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

  strong-recursion-principle-subuniverse-modality : UU (lsuc l1 ⊔ l2)
  strong-recursion-principle-subuniverse-modality =
    (X Y : UU l1) → retraction (unit-○ {Y}) →
    section-Π (precomp {A = X} unit-○ Y)

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
  where

  rec-subuniverse-ind-subuniverse-modality :
    ind-subuniverse-modality unit-○ → rec-subuniverse-modality unit-○
  rec-subuniverse-ind-subuniverse-modality ind-○ X Y is-modal-Y =
    ind-○ X (λ _ → Y) (λ _ → is-modal-Y)

  compute-rec-subuniverse-compute-ind-subuniverse-modality :
    (ind-○ : ind-subuniverse-modality unit-○) →
    compute-ind-subuniverse-modality unit-○ ind-○ →
    compute-rec-subuniverse-modality unit-○
      ( rec-subuniverse-ind-subuniverse-modality ind-○)
  compute-rec-subuniverse-compute-ind-subuniverse-modality
    ind-○ compute-ind-○ X Y is-modal-Y =
      compute-ind-○ X (λ _ → Y) (λ _ → is-modal-Y)

  recursion-principle-induction-principle-subuniverse-modality :
    induction-principle-subuniverse-modality unit-○ →
    recursion-principle-subuniverse-modality unit-○
  recursion-principle-induction-principle-subuniverse-modality
    I X Y is-modal-Y = I X (λ _ → Y) (λ _ → is-modal-Y)
```

### Subuniverse induction from strong subuniverse induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-subuniverse-strong-ind-subuniverse-modality :
    strong-ind-subuniverse-modality unit-○ → ind-subuniverse-modality unit-○
  ind-subuniverse-strong-ind-subuniverse-modality ind-○ X P is-modal-P =
    ind-○ X P (retraction-is-equiv ∘ is-modal-P)

  compute-ind-subuniverse-strong-ind-subuniverse-modality :
    (ind-○ : strong-ind-subuniverse-modality unit-○) →
    compute-strong-ind-subuniverse-modality unit-○ ind-○ →
    compute-ind-subuniverse-modality unit-○
      ( ind-subuniverse-strong-ind-subuniverse-modality ind-○)
  compute-ind-subuniverse-strong-ind-subuniverse-modality
    ind-○ compute-ind-○ X P is-modal-P =
    compute-ind-○ X P (retraction-is-equiv ∘ is-modal-P)

  induction-principle-strong-induction-principle-subuniverse-modality :
    strong-induction-principle-subuniverse-modality unit-○ →
    induction-principle-subuniverse-modality unit-○
  induction-principle-strong-induction-principle-subuniverse-modality
    I X P is-modal-P = I X P (retraction-is-equiv ∘ is-modal-P)
```

### Subuniverse recursion from strong subuniverse recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-subuniverse-strong-rec-subuniverse-modality :
    strong-rec-subuniverse-modality unit-○ → rec-subuniverse-modality unit-○
  rec-subuniverse-strong-rec-subuniverse-modality rec-○ X Y is-modal-Y =
    rec-○ X Y (retraction-is-equiv is-modal-Y)

  compute-rec-subuniverse-strong-rec-subuniverse-modality :
    (rec-○ : strong-rec-subuniverse-modality unit-○)
    (compute-rec-○ : compute-strong-rec-subuniverse-modality unit-○ rec-○) →
    compute-rec-subuniverse-modality unit-○
      ( rec-subuniverse-strong-rec-subuniverse-modality rec-○)
  compute-rec-subuniverse-strong-rec-subuniverse-modality
    rec-○ compute-rec-○ X Y is-modal-Y =
    compute-rec-○ X Y (retraction-is-equiv is-modal-Y)

  recursion-principle-strong-recursion-principle-subuniverse-modality :
    strong-recursion-principle-subuniverse-modality unit-○ →
    recursion-principle-subuniverse-modality unit-○
  recursion-principle-strong-recursion-principle-subuniverse-modality
    I X Y is-modal-Y =
    I X Y (retraction-is-equiv is-modal-Y)
```

### Subuniverse induction from modal induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-ind-subuniverse-ind-modality :
    ind-modality unit-○ → strong-ind-subuniverse-modality unit-○
  strong-ind-subuniverse-ind-modality ind-○ X P is-premodal-P f x' =
    map-retraction unit-○ (is-premodal-P x') (ind-○ X P (unit-○ ∘ f) x')

  compute-strong-ind-subuniverse-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality ind-○)
  compute-strong-ind-subuniverse-ind-modality
    ind-○ compute-ind-○ X P is-premodal-P f x =
    ( ap
      ( map-retraction unit-○ (is-premodal-P (unit-○ x)))
      ( compute-ind-○ X P (unit-○ ∘ f) x)) ∙
    ( is-retraction-map-retraction unit-○ (is-premodal-P (unit-○ x)) (f x))

  strong-induction-principle-subuniverse-induction-principle-modality :
    induction-principle-modality unit-○ →
    strong-induction-principle-subuniverse-modality unit-○
  pr1
    ( strong-induction-principle-subuniverse-induction-principle-modality
      I X P is-modal-P) =
    strong-ind-subuniverse-ind-modality
      ( ind-induction-principle-modality unit-○ I) X P is-modal-P
  pr2
    ( strong-induction-principle-subuniverse-induction-principle-modality
        I X P is-modal-P) =
    compute-strong-ind-subuniverse-ind-modality
    ( ind-induction-principle-modality unit-○ I)
    ( compute-ind-induction-principle-modality unit-○ I)
    ( X)
    ( P)
    ( is-modal-P)

  ind-subuniverse-ind-modality :
    ind-modality unit-○ → ind-subuniverse-modality unit-○
  ind-subuniverse-ind-modality ind-○ =
    ind-subuniverse-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality ind-○)

  compute-ind-subuniverse-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-ind-subuniverse-modality unit-○
      ( ind-subuniverse-ind-modality ind-○)
  compute-ind-subuniverse-ind-modality ind-○ compute-ind-○ =
    compute-ind-subuniverse-strong-ind-subuniverse-modality unit-○
      ( strong-ind-subuniverse-ind-modality ind-○)
      ( compute-strong-ind-subuniverse-ind-modality ind-○ compute-ind-○)

  induction-principle-subuniverse-induction-principle-modality :
    induction-principle-modality unit-○ →
    induction-principle-subuniverse-modality unit-○
  pr1
    ( induction-principle-subuniverse-induction-principle-modality
        I X P is-modal-P) =
    ind-subuniverse-ind-modality
      ( ind-induction-principle-modality unit-○ I)
      ( X)
      ( P)
      ( is-modal-P)
  pr2
    ( induction-principle-subuniverse-induction-principle-modality
        I X P is-modal-P) =
    compute-ind-subuniverse-ind-modality
      ( ind-induction-principle-modality unit-○ I)
      ( compute-ind-induction-principle-modality unit-○ I)
      ( X)
      ( P)
      ( is-modal-P)
```

### Subuniverse recursion from modal recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  strong-rec-subuniverse-rec-modality :
    rec-modality unit-○ → strong-rec-subuniverse-modality unit-○
  strong-rec-subuniverse-rec-modality rec-○ X Y is-premodal-Y f x' =
    map-retraction unit-○ (is-premodal-Y) (rec-○ X Y (unit-○ ∘ f) x')

  compute-strong-rec-subuniverse-rec-modality :
    (rec-○ : rec-modality unit-○) →
    compute-rec-modality unit-○ rec-○ →
    compute-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality rec-○)
  compute-strong-rec-subuniverse-rec-modality
    rec-○ compute-rec-○ X Y is-premodal-Y f x =
    ( ap
      ( map-retraction unit-○ (is-premodal-Y))
      ( compute-rec-○ X Y (unit-○ ∘ f) x)) ∙
    ( is-retraction-map-retraction unit-○ (is-premodal-Y) (f x))

  strong-recursion-principle-subuniverse-recursion-principle-modality :
    recursion-principle-modality unit-○ →
    strong-recursion-principle-subuniverse-modality unit-○
  pr1
    ( strong-recursion-principle-subuniverse-recursion-principle-modality
        I X Y is-premodal-Y) =
    strong-rec-subuniverse-rec-modality
      ( rec-recursion-principle-modality unit-○ I)
      ( X)
      ( Y)
      ( is-premodal-Y)
  pr2
    ( strong-recursion-principle-subuniverse-recursion-principle-modality
        I X Y is-premodal-Y) =
    compute-strong-rec-subuniverse-rec-modality
      ( rec-recursion-principle-modality unit-○ I)
      ( compute-rec-recursion-principle-modality unit-○ I)
      ( X)
      ( Y)
      ( is-premodal-Y)

  rec-subuniverse-rec-modality :
    rec-modality unit-○ → rec-subuniverse-modality unit-○
  rec-subuniverse-rec-modality rec-○ =
    rec-subuniverse-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality rec-○)

  compute-rec-subuniverse-rec-modality :
    (rec-○ : rec-modality unit-○) →
    compute-rec-modality unit-○ rec-○ →
    compute-rec-subuniverse-modality unit-○ (rec-subuniverse-rec-modality rec-○)
  compute-rec-subuniverse-rec-modality rec-○ compute-rec-○ =
    compute-rec-subuniverse-strong-rec-subuniverse-modality unit-○
      ( strong-rec-subuniverse-rec-modality rec-○)
      ( compute-strong-rec-subuniverse-rec-modality rec-○ compute-rec-○)

  recursion-principle-subuniverse-recursion-principle-modality :
    recursion-principle-modality unit-○ →
    recursion-principle-subuniverse-modality unit-○
  pr1
    ( recursion-principle-subuniverse-recursion-principle-modality
        I X Y is-modal-Y) =
    rec-subuniverse-rec-modality
      ( rec-recursion-principle-modality unit-○ I) X Y is-modal-Y
  pr2
    ( recursion-principle-subuniverse-recursion-principle-modality
        I X Y is-modal-Y) =
    compute-rec-subuniverse-rec-modality
      ( rec-recursion-principle-modality unit-○ I)
      ( compute-rec-recursion-principle-modality unit-○ I)
      ( X)
      ( Y)
      ( is-modal-Y)
```

## See also

- [Reflective subuniverses](orthogonal-factorization-systems.reflective-subuniverses.md)
