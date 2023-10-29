# The sharp modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.sharp-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.modal-subuniverse-induction
```

</details>

## Idea

The **sharp modality `♯`** is an axiomatized monadic modality we postulate as a
right adjoint to the [flat modality](modal-type-theory.flat-modality.md).

In this file, we only postulate that `♯` is a modal operator that has a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).
In the file about [codiscrete types](modal-type-theory.codiscrete-types.md), we
postulate that the subuniverse of sharp modal types has appropriate closure
properties. In
[the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md), we
postulate that it has the appropriate relation to the flat modality, making it a
lex modality. Please note that there is some redundancy between the postulated
axioms, and they may be subject to change in the future.

## Postulates

```agda
postulate
  ♯ : {l : Level} (A : UU l) → UU l

  @♭ unit-♯ : {l : Level} {A : UU l} → A → ♯ A

  ind-♯ :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
    ((x : A) → ♯ (C (unit-♯ x))) →
    ((x : ♯ A) → ♯ (C x))

  compute-ind-♯ :
    {l1 l2 : Level} {A : UU l1} (C : ♯ A → UU l2)
    (f : (x : A) → ♯ (C (unit-♯ x))) →
    (ind-♯ C f ∘ unit-♯) ~ f
```

## Definitions

### The sharp modal operator

```agda
♯-locally-small-operator-modality :
  (l : Level) → locally-small-operator-modality l l l
pr1 (♯-locally-small-operator-modality l) = ♯ {l}
pr2 (♯-locally-small-operator-modality l) A = is-locally-small' {l} {♯ A}
```

### The sharp induction principle

```agda
induction-principle-♯ : {l : Level} → induction-principle-modality {l} unit-♯
pr1 (induction-principle-♯ P) = ind-♯ P
pr2 (induction-principle-♯ P) = compute-ind-♯ P

strong-induction-principle-subuniverse-♯ :
  {l : Level} → strong-induction-principle-subuniverse-modality {l} unit-♯
strong-induction-principle-subuniverse-♯ =
  strong-induction-principle-subuniverse-induction-principle-modality
    ( unit-♯)
    ( induction-principle-♯)

strong-ind-subuniverse-♯ :
  {l : Level} → strong-ind-subuniverse-modality {l} unit-♯
strong-ind-subuniverse-♯ =
  strong-ind-strong-induction-principle-subuniverse-modality
    ( unit-♯)
    ( strong-induction-principle-subuniverse-♯)

compute-strong-ind-subuniverse-♯ :
  {l : Level} →
  compute-strong-ind-subuniverse-modality {l} unit-♯ strong-ind-subuniverse-♯
compute-strong-ind-subuniverse-♯ =
  compute-strong-ind-strong-induction-principle-subuniverse-modality
    ( unit-♯)
    ( strong-induction-principle-subuniverse-♯)

induction-principle-subuniverse-♯ :
  {l : Level} → induction-principle-subuniverse-modality {l} unit-♯
induction-principle-subuniverse-♯ =
  induction-principle-subuniverse-induction-principle-modality
    ( unit-♯)
    ( induction-principle-♯)

ind-subuniverse-♯ :
  {l : Level} → ind-subuniverse-modality {l} unit-♯
ind-subuniverse-♯ =
  ind-induction-principle-subuniverse-modality
    ( unit-♯)
    ( induction-principle-subuniverse-♯)

compute-ind-subuniverse-♯ :
  {l : Level} → compute-ind-subuniverse-modality {l} unit-♯ ind-subuniverse-♯
compute-ind-subuniverse-♯ =
  compute-ind-induction-principle-subuniverse-modality
    ( unit-♯)
    ( induction-principle-subuniverse-♯)
```

### Sharp recursion

```agda
rec-♯ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → ♯ B) → (♯ A → ♯ B)
rec-♯ {B = B} = ind-♯ (λ _ → B)

compute-rec-♯ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → ♯ B) →
  (rec-♯ f ∘ unit-♯) ~ f
compute-rec-♯ {B = B} = compute-ind-♯ (λ _ → B)

recursion-principle-♯ : {l : Level} → recursion-principle-modality {l} unit-♯
pr1 (recursion-principle-♯) = rec-♯
pr2 (recursion-principle-♯) = compute-rec-♯

strong-recursion-principle-subuniverse-♯ :
  {l : Level} → strong-recursion-principle-subuniverse-modality {l} unit-♯
strong-recursion-principle-subuniverse-♯ =
  strong-recursion-principle-subuniverse-recursion-principle-modality
    ( unit-♯)
    ( recursion-principle-♯)

strong-rec-subuniverse-♯ :
  {l : Level} → strong-rec-subuniverse-modality {l} unit-♯
strong-rec-subuniverse-♯ =
  strong-rec-strong-recursion-principle-subuniverse-modality
    ( unit-♯)
    ( strong-recursion-principle-subuniverse-♯)

compute-strong-rec-subuniverse-♯ :
  {l : Level} →
  compute-strong-rec-subuniverse-modality {l} unit-♯ strong-rec-subuniverse-♯
compute-strong-rec-subuniverse-♯ =
  compute-strong-rec-strong-recursion-principle-subuniverse-modality
    ( unit-♯)
    ( strong-recursion-principle-subuniverse-♯)

recursion-principle-subuniverse-♯ :
  {l : Level} → recursion-principle-subuniverse-modality {l} unit-♯
recursion-principle-subuniverse-♯ =
  recursion-principle-subuniverse-recursion-principle-modality
    ( unit-♯)
    ( recursion-principle-♯)

rec-subuniverse-♯ :
  {l : Level} → rec-subuniverse-modality {l} unit-♯
rec-subuniverse-♯ =
  rec-recursion-principle-subuniverse-modality
    ( unit-♯)
    ( recursion-principle-subuniverse-♯)

compute-rec-subuniverse-♯ :
  {l : Level} → compute-rec-subuniverse-modality {l} unit-♯ rec-subuniverse-♯
compute-rec-subuniverse-♯ =
  compute-rec-recursion-principle-subuniverse-modality
    ( unit-♯)
    ( recursion-principle-subuniverse-♯)
```

### Action on maps

```agda
ap-♯ : {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → (♯ A → ♯ B)
ap-♯ f = rec-♯ (unit-♯ ∘ f)
```

## See also

- In [codiscrete types](modal-type-theory.codiscrete-types.md), we postulate
  that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).
- and in [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md)
  we moreover postulate that the sharp modality is right adjoint to the
  [flat modality](modal-type-theory.flat-modality.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
- Felix Cherubini, _DCHoTT-Agda_/Im.agda, file in GitHub repository
  (<https://github.com/felixwellen/DCHoTT-Agda/blob/master/Im.agda>)
