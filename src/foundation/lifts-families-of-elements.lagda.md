# Lifts of families of elements

```agda
module foundation.lifts-families-of-elements where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.function-extensionality
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.transport-along-homotopies
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Idea

Consider a map `h : A → X` and a type family `P` over `X`, which we think of as
a family of elements in `X`. A **lift of families of elements** into `P` along
`h` is a family of elements `(a : A) → P (h a)`.

## Definitions

### Lifts of families of elements

```agda
module _
  {l1 l2 l3 : Level} (A : UU l1) {X : UU l2} (P : X → UU l3)
  where

  lift-family-of-elements :
    (A → X) → UU (l1 ⊔ l3)
  lift-family-of-elements h = (a : A) → P (h a)
```

### Precomposition of lifts by ordinary functions

```agda
precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (f : A → B) → (h : B → X) →
  (lift-family-of-elements B P h) → (lift-family-of-elements A P (h ∘ f))
precompose-lifts P f h h' a = h' (f a)
```

## Properties

### Transporting lifts along homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (h : B → X)
  where

  tr-lift-family-of-elements :
    {f g : A → B} (H : f ~ g) →
    lift-family-of-elements A P (h ∘ f) → lift-family-of-elements A P (h ∘ g)
  tr-lift-family-of-elements = tr-htpy (λ _ → P ∘ h)

  COMPUTE-TR-LIFT-FAMILY-OF-ELEMENTS :
    {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l4)
  COMPUTE-TR-LIFT-FAMILY-OF-ELEMENTS =
    statement-compute-tr-htpy (λ _ → P ∘ h)

  base-case-compute-tr-lift-family-of-elements :
    {f : A → B} →
    COMPUTE-TR-LIFT-FAMILY-OF-ELEMENTS (refl-htpy' f)
  base-case-compute-tr-lift-family-of-elements =
    base-case-compute-tr-htpy (λ _ → P ∘ h)

  abstract
    compute-tr-lift-family-of-elements :
      {f g : A → B} (H : f ~ g) →
      COMPUTE-TR-LIFT-FAMILY-OF-ELEMENTS H
    compute-tr-lift-family-of-elements {f} =
      compute-tr-htpy (λ _ → P ∘ h)

    compute-tr-left-family-of-elements-refl-htpy :
      {f : A → B} →
      compute-tr-lift-family-of-elements (refl-htpy' f) ＝
      base-case-compute-tr-lift-family-of-elements
    compute-tr-left-family-of-elements-refl-htpy =
      compute-tr-htpy-refl-htpy (λ _ → P ∘ h)
```

Given two homotopic maps, their precomposition functions have different
codomains. However, there is a commuting triangle. We obtain this triangle by
homotopy induction.

```agda
module _
  { l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  ( P : X → UU l4)
  where
  
  TRIANGLE-PRECOMPOSE-LIFTS :
    {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  TRIANGLE-PRECOMPOSE-LIFTS {f} {g} H =
    (h : B → X) →
    coherence-triangle-maps' 
      ( precompose-lifts P g h)
      ( tr (λ u → (x : A) → P (u x)) (eq-htpy (h ·l H)))
      -- ( tr (lift-family-of-elements A P) (eq-htpy (h ·l H)))
      ( precompose-lifts P f h)

  triangle-precompose-lifts-refl-htpy :
    (f : A → B) → TRIANGLE-PRECOMPOSE-LIFTS (refl-htpy' f)
  triangle-precompose-lifts-refl-htpy f h h' =
    base-case-compute-tr-lift-family-of-elements P h (h' ∘ f)

triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  TRIANGLE-PRECOMPOSE-LIFTS P H
triangle-precompose-lifts {A = A} P {f} =
  ind-htpy f
    ( λ g H → TRIANGLE-PRECOMPOSE-LIFTS P H)
    ( triangle-precompose-lifts-refl-htpy P f)

compute-triangle-precompose-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  Id
    ( triangle-precompose-lifts P (refl-htpy' f))
    ( triangle-precompose-lifts-refl-htpy P f)
compute-triangle-precompose-lifts P f =
  compute-ind-htpy f
    ( λ g → TRIANGLE-PRECOMPOSE-LIFTS P)
    ( triangle-precompose-lifts-refl-htpy P f)
```

There is a similar commuting triangle with the computed transport function. This
time we don't use homotopy induction to construct the homotopy. We give an
explicit definition instead.

```agda
triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) → (h : B → X) →
  ( (tr-lift-family-of-elements P h H) ∘ (precompose-lifts P f h)) ~
  ( precompose-lifts P g h)
triangle-precompose-lifts' P H h k = eq-htpy (λ a → apd k (H a))

compute-triangle-precompose-lifts' :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) → (h : B → X) →
  ( triangle-precompose-lifts' P (refl-htpy' f) h) ~
  ( refl-htpy' ( precompose-lifts P f h))
compute-triangle-precompose-lifts' P f h k = eq-htpy-refl-htpy _
```

There is a coherence between the two commuting triangles. This coherence is
again constructed by homotopy induction.

```agda
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS {A = A} {B} {X} P {f} {g} H =
  (h : B → X) →
    ( triangle-precompose-lifts P H h) ~
    ( ( ( compute-tr-lift-family-of-elements P h H) ·r
        ( precompose-lifts P f h)) ∙h
      ( triangle-precompose-lifts' P H h))

coherence-triangle-precompose-lifts-refl-htpy :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  (f : A → B) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P (refl-htpy' f)
coherence-triangle-precompose-lifts-refl-htpy P f h =
  ( htpy-eq (htpy-eq (compute-triangle-precompose-lifts P f) h)) ∙h
  ( ( ( inv-htpy-right-unit-htpy) ∙h
      ( ap-concat-htpy
        ( λ h' →
          base-case-compute-tr-lift-family-of-elements P h (λ a → h' (f a)))
        ( refl-htpy)
        ( triangle-precompose-lifts' P refl-htpy h)
        ( inv-htpy (compute-triangle-precompose-lifts' P f h)))) ∙h
    ( htpy-eq
      ( ap
        ( λ t →
          ( t ·r (precompose-lifts P f h)) ∙h
          ( triangle-precompose-lifts' P refl-htpy h))
        ( inv (compute-tr-left-family-of-elements-refl-htpy P h)))))

abstract
  coherence-triangle-precompose-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    {f g : A → B} (H : f ~ g) → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H
  coherence-triangle-precompose-lifts P {f} =
    ind-htpy f
      ( λ g H → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H)
      ( coherence-triangle-precompose-lifts-refl-htpy P f)

  compute-coherence-triangle-precompose-lifts :
    {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
    (f : A → B) →
      Id ( coherence-triangle-precompose-lifts P (refl-htpy' f))
          ( coherence-triangle-precompose-lifts-refl-htpy P f)
  compute-coherence-triangle-precompose-lifts P f =
    compute-ind-htpy f
      ( λ g H → COHERENCE-TRIANGLE-PRECOMPOSE-LIFTS P H)
      ( coherence-triangle-precompose-lifts-refl-htpy P f)

total-lifts :
  {l1 l2 l3 : Level} (A : UU l1) {X : UU l2} (P : X → UU l3) →
  UU (l1 ⊔ l2 ⊔ l3)
total-lifts A {X} P = universally-structured-Π {A = A} {B = λ a → X} (λ a → P)

precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) → (A → B) →
  total-lifts B P → total-lifts A P
precompose-total-lifts {A = A} P f =
  map-Σ
    ( λ h → (a : A) → P (h a))
    ( λ h → h ∘ f)
    ( precompose-lifts P f)

coherence-square-map-inv-distributive-Π-Σ :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) (f : A → B) →
  coherence-square-maps
    ( precompose-total-lifts P f)
    ( map-inv-distributive-Π-Σ {A = B} {B = λ x → X} {C = λ x y → P y})
    ( map-inv-distributive-Π-Σ)
    ( λ h → h ∘ f)
coherence-square-map-inv-distributive-Π-Σ P f = refl-htpy
```

Our goal is now to produce a homotopy between `precompose-total-lifts P f` and
`precompose-total-lifts P g` for homotopic maps `f` and `g`, and a coherence
filling a cylinder.

```agda
HTPY-PRECOMPOSE-TOTAL-LIFTS :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3}
  (P : X → UU l4) {f g : A → B} (H : f ~ g) →
  UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
HTPY-PRECOMPOSE-TOTAL-LIFTS P {f} {g} H =
  (precompose-total-lifts P f) ~ (precompose-total-lifts P g)

htpy-precompose-total-lifts :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} (P : X → UU l4)
  {f g : A → B} (H : f ~ g) → HTPY-PRECOMPOSE-TOTAL-LIFTS P H
htpy-precompose-total-lifts {A = A} {B} P {f} {g} H =
  htpy-map-Σ
    ( lift-family-of-elements A P)
    ( λ h → {!!}) -- ( λ h → eq-htpy (h ·l H))
    ( precompose-lifts P f)
    ( triangle-precompose-lifts P H) -- ( triangle-precompose-lifts P H)
    ∙h {!!}
```
