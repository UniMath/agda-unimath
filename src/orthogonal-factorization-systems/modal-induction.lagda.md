# Modal induction

```agda
open import foundation.function-extensionality-axiom

module
  orthogonal-factorization-systems.modal-induction
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.function-extensionality funext

open import foundation.function-types funext
open import foundation.functoriality-dependent-function-types funext
open import foundation.functoriality-dependent-pair-types funext
open import foundation.homotopies funext
open import foundation.identity-types funext
open import foundation.multivariable-sections funext
open import foundation.precomposition-dependent-functions funext
open import foundation.precomposition-functions funext
open import foundation.retractions funext
open import foundation.sections funext
open import foundation.telescopes
open import foundation.type-theoretic-principle-of-choice funext
open import foundation.unit-type
open import foundation.universe-levels

open import orthogonal-factorization-systems.modal-operators funext
```

</details>

## Idea

Given a [modal operator](orthogonal-factorization-systems.modal-operators.md)
`○` and a modal unit, a **modal induction principle** for the modality is a
[section of maps of maps](foundation.multivariable-sections.md):

```text
  multivariable-section 1 (precomp-Π unit-○ (○ ∘ P))
```

where

```text
  precomp-Π unit-○ (○ ∘ P) : ((x' : ○ X) → ○ (P x')) → (x : X) → ○ (P (unit-○ x))
```

for all families `P` over some `○ X`.

Note that for such principles to coincide with
[modal subuniverse induction](orthogonal-factorization-systems.modal-subuniverse-induction.md),
the modality must be idempotent.

## Definition

### Modal induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ind-modality : UU (lsuc l1 ⊔ l2)
  ind-modality =
    {X : UU l1} (P : ○ X → UU l1) →
    ((x : X) → ○ (P (unit-○ x))) →
    (x' : ○ X) → ○ (P x')

  compute-ind-modality : ind-modality → UU (lsuc l1 ⊔ l2)
  compute-ind-modality ind-○ =
    {X : UU l1} (P : ○ X → UU l1) →
    (f : (x : X) → ○ (P (unit-○ x))) →
    (x : X) → ind-○ P f (unit-○ x) ＝ f x

  induction-principle-modality : UU (lsuc l1 ⊔ l2)
  induction-principle-modality =
    {X : UU l1} (P : ○ X → UU l1) →
    multivariable-section 1 (precomp-Π unit-○ (○ ∘ P))

  ind-induction-principle-modality : induction-principle-modality → ind-modality
  ind-induction-principle-modality I P =
    map-multivariable-section 1 (precomp-Π unit-○ (○ ∘ P)) (I P)

  compute-ind-induction-principle-modality :
    (I : induction-principle-modality) →
    compute-ind-modality (ind-induction-principle-modality I)
  compute-ind-induction-principle-modality I P =
    is-multivariable-section-map-multivariable-section 1
      ( precomp-Π unit-○ (○ ∘ P))
      ( I P)
```

### Modal recursion

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-modality : UU (lsuc l1 ⊔ l2)
  rec-modality = {X Y : UU l1} → (X → ○ Y) → ○ X → ○ Y

  compute-rec-modality : rec-modality → UU (lsuc l1 ⊔ l2)
  compute-rec-modality rec-○ =
    {X Y : UU l1} →
    (f : X → ○ Y) →
    (x : X) → rec-○ f (unit-○ x) ＝ f x

  recursion-principle-modality : UU (lsuc l1 ⊔ l2)
  recursion-principle-modality =
    {X Y : UU l1} → multivariable-section 1 (precomp {A = X} unit-○ (○ Y))

  rec-recursion-principle-modality : recursion-principle-modality → rec-modality
  rec-recursion-principle-modality I {Y = Y} =
    map-multivariable-section 1 (precomp unit-○ (○ Y)) I

  compute-rec-recursion-principle-modality :
    (I : recursion-principle-modality) →
    compute-rec-modality (rec-recursion-principle-modality I)
  compute-rec-recursion-principle-modality I {Y = Y} =
    is-multivariable-section-map-multivariable-section 1
      ( precomp unit-○ (○ Y)) I
```

## Properties

### Modal recursion from induction

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  rec-ind-modality : ind-modality unit-○ → rec-modality unit-○
  rec-ind-modality ind {Y = Y} = ind (λ _ → Y)

  compute-rec-compute-ind-modality :
    (ind-○ : ind-modality unit-○) →
    compute-ind-modality unit-○ ind-○ →
    compute-rec-modality unit-○ (rec-ind-modality ind-○)
  compute-rec-compute-ind-modality ind-○ compute-ind-○ {Y = Y} =
    compute-ind-○ (λ _ → Y)

  recursion-principle-induction-principle-modality :
    induction-principle-modality unit-○ → recursion-principle-modality unit-○
  recursion-principle-induction-principle-modality I {Y = Y} = I (λ _ → Y)
```

### Modal induction gives an inverse to the unit

```agda
is-section-ind-modality :
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  {X : UU l1} {P : ○ X → UU l1} → (precomp-Π unit-○ (○ ∘ P) ∘ ind-○ P) ~ id
is-section-ind-modality unit-○ ind-○ compute-ind-○ {X} {P} =
  eq-htpy ∘ compute-ind-○ P

is-retraction-ind-id-modality :
  {l : Level}
  {○ : operator-modality l l}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  {X : UU l} → (ind-○ (λ _ → X) id ∘ unit-○) ~ id
is-retraction-ind-id-modality {○ = ○} unit-○ ind-○ compute-ind-○ {X} =
  compute-ind-○ (λ _ → X) id

module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (rec-○ : rec-modality unit-○)
  (compute-rec-○ : compute-rec-modality unit-○ rec-○)
  where

  is-retraction-rec-map-modality :
    {X Y : UU l1} (f : ○ X → Y) (r : retraction f) →
    (rec-○ (map-retraction f r) ∘ (unit-○ ∘ f)) ~ id
  is-retraction-rec-map-modality {X} {Y} f r =
    ( compute-rec-○ (map-retraction f r) ∘ f) ∙h
    ( is-retraction-map-retraction f r)

  retraction-rec-map-modality :
    {X Y : UU l1} (f : ○ X → Y) →
    retraction f → retraction (unit-○ ∘ f)
  pr1 (retraction-rec-map-modality {X} {Y} f r) = rec-○ (map-retraction f r)
  pr2 (retraction-rec-map-modality f r) = is-retraction-rec-map-modality f r

  section-rec-map-modality :
    {X Y : UU l1} (f : X → ○ Y) →
    section f → section (rec-○ f)
  pr1 (section-rec-map-modality f s) = unit-○ ∘ map-section f s
  pr2 (section-rec-map-modality {X} {Y} f s) =
    (compute-rec-○ f ∘ map-section f s) ∙h is-section-map-section f s
```

### A modal induction principle consists precisely of an induction rule and a computation rule

```agda
equiv-section-unit-induction-principle-modality :
  { l1 l2 : Level}
  { ○ : operator-modality l1 l2}
  ( unit-○ : unit-modality ○) →
  ( induction-principle-modality unit-○) ≃
  Σ ( {X : UU l1} (P : ○ X → UU l1) →
      ((x : X) → ○ (P (unit-○ x))) → (x' : ○ X) → ○ (P x'))
    ( λ I →
      {X : UU l1} (P : ○ X → UU l1) (f : (x : X) → ○ (P (unit-○ x))) →
      I P f ∘ unit-○ ~ f)
equiv-section-unit-induction-principle-modality unit-○ =
  distributive-implicit-Π-Σ ∘e
  equiv-implicit-Π-equiv-family (λ _ → distributive-Π-Σ)

equiv-section-unit-recursion-principle-modality :
  { l1 l2 : Level}
  { ○ : operator-modality l1 l2}
  ( unit-○ : unit-modality ○) →
  ( recursion-principle-modality unit-○) ≃
    Σ ( {X Y : UU l1} → (X → ○ Y) → ○ X → ○ Y)
    ( λ I → {X Y : UU l1} (f : X → ○ Y) → I f ∘ unit-○ ~ f)
equiv-section-unit-recursion-principle-modality unit-○ =
  distributive-implicit-Π-Σ ∘e
  equiv-implicit-Π-equiv-family (λ _ → distributive-implicit-Π-Σ)
```

### The modal operator's action on maps

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  where

  ap-map-rec-modality :
    rec-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-map-rec-modality rec-○ f = rec-○ (unit-○ ∘ f)

  ap-map-ind-modality :
    ind-modality unit-○ → {X Y : UU l1} → (X → Y) → ○ X → ○ Y
  ap-map-ind-modality ind-○ =
    ap-map-rec-modality (rec-ind-modality unit-○ ind-○)
```

### Naturality of the unit

For every `f : X → Y` there is an associated
[naturality square](foundation-core.commuting-squares-of-maps.md)

```text
         f
    X ------> Y
    |         |
    |         |
    ∨         ∨
   ○ X ----> ○ Y.
        ○ f
```

```agda
module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (rec-○ : rec-modality unit-○)
  (compute-rec-○ : compute-rec-modality unit-○ rec-○)
  where

  naturality-unit-rec-modality :
    {X Y : UU l1} (f : X → Y) →
    (ap-map-rec-modality unit-○ rec-○ f ∘ unit-○) ~ (unit-○ ∘ f)
  naturality-unit-rec-modality f =
    compute-rec-○ (unit-○ ∘ f)

  naturality-unit-rec-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-○ x ＝ unit-○ x' → unit-○ (f x) ＝ unit-○ (f x')
  naturality-unit-rec-modality' f {x} {x'} p =
    ( inv (naturality-unit-rec-modality f x)) ∙
    ( ( ap (ap-map-rec-modality unit-○ rec-○ f) p) ∙
      ( naturality-unit-rec-modality f x'))

module _
  {l1 l2 : Level}
  {○ : operator-modality l1 l2}
  (unit-○ : unit-modality ○)
  (ind-○ : ind-modality unit-○)
  (compute-ind-○ : compute-ind-modality unit-○ ind-○)
  where

  naturality-unit-ind-modality :
    {X Y : UU l1} (f : X → Y) →
    ap-map-ind-modality unit-○ ind-○ f ∘ unit-○ ~ unit-○ ∘ f
  naturality-unit-ind-modality =
    naturality-unit-rec-modality unit-○
      ( rec-ind-modality unit-○ ind-○)
      ( compute-rec-compute-ind-modality unit-○ ind-○ compute-ind-○)

  naturality-unit-ind-modality' :
    {X Y : UU l1} (f : X → Y) {x x' : X} →
    unit-○ x ＝ unit-○ x' → unit-○ (f x) ＝ unit-○ (f x')
  naturality-unit-ind-modality' =
    naturality-unit-rec-modality' unit-○
      ( rec-ind-modality unit-○ ind-○)
      ( compute-rec-compute-ind-modality unit-○ ind-○ compute-ind-○)
```

## See also

- [Functoriality of higher modalities](orthogonal-factorization-systems.functoriality-higher-modalities.md)
- [Modal subuniverse induction](orthogonal-factorization-systems.modal-subuniverse-induction.md)
