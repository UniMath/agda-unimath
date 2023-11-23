# The flat-sharp adjunction

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-sharp-adjunction where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.locally-small-types
open import foundation.multivariable-sections
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import modal-type-theory.codiscrete-types
open import modal-type-theory.crisp-identity-types
open import modal-type-theory.flat-modality
open import modal-type-theory.sharp-modality

open import orthogonal-factorization-systems.locally-small-modal-operators
open import orthogonal-factorization-systems.modal-induction
open import orthogonal-factorization-systems.uniquely-eliminating-modalities
```

</details>

## Idea

We postulate that the [flat modality](modal-type-theory.flat-modality.md) `♭` is
a crisp left adjoint to the
[sharp modality](modal-type-theory.sharp-modality.md) `♯`.

In [The sharp modality](modal-type-theory.sharp-modality.md) we postulated that
`♯` is a modal operator that has a
[modal induction principle](orthogonal-factorization-systems.modal-induction.md).
In the file [Codiscrete types](modal-type-theory.codiscrete-types.md), we
postulated that the [subuniverse](foundation.subuniverses.md) of sharp modal types has appropriate closure
properties. Please note that there is some redundancy between the postulated
axioms, and they may be subject to change in the future.

## Postulates

### Crisp induction for `♯`

Codiscrete types are local at the flat counit.

```agda
postulate
  crisp-ind-♯ :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2) →
    ((x : A) → is-codiscrete (C x)) →
    ((@♭ x : A) → C x) → (x : A) → C x

  compute-crisp-ind-♯ :
    {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : A → UU l2)
    (is-codiscrete-C : (x : A) → is-codiscrete (C x))
    (f : (@♭ x : A) → C x) →
    (@♭ x : A) → crisp-ind-♯ C is-codiscrete-C f x ＝ f x
```

### Crisp elimination of `♯`

```agda
postulate
  crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A

  compute-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) → (crisp-elim-♯ (unit-♯ x)) ＝ x

  uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : ♯ A) → unit-♯ (crisp-elim-♯ x) ＝ x

  coherence-uniqueness-crisp-elim-♯ :
    {@♭ l : Level} {@♭ A : UU l} (@♭ x : A) →
    uniqueness-crisp-elim-♯ (unit-♯ x) ＝ ap unit-♯ (compute-crisp-elim-♯ x)
```

## Definitions

### Crisp recursion for `♯`

```agda
crisp-rec-♯ :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : UU l2) →
  (is-codiscrete C) →
  ((@♭ x : A) → C) → A → C
crisp-rec-♯ C is-codiscrete-C =
  crisp-ind-♯ (λ _ → C) (λ _ → is-codiscrete-C)

compute-crisp-rec-♯ :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : UU l2)
  (is-codiscrete-C : is-codiscrete C)
  (f : (@♭ x : A) → C) →
  (@♭ x : A) → crisp-rec-♯ C is-codiscrete-C f x ＝ f x
compute-crisp-rec-♯ C is-codiscrete-C =
  compute-crisp-ind-♯ (λ _ → C) (λ _ → is-codiscrete-C)
```

## Properties

```agda
crisp-tr-sharp :
  {@♭ l : Level} {@♭ A : UU l} {B : UU l} → (p : A ＝ B) →
  {@♭ x : ♯ A} → unit-♯ (tr (λ X → X) p (crisp-elim-♯ x)) ＝ tr ♯ p x
crisp-tr-sharp refl {x} = uniqueness-crisp-elim-♯ x
```

### Crisp induction on `♯` implies typal induction

```agda
ind-crisp-ind-♯ :
  {@♭ l1 : Level} {l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
  ((x : ♯ A) → is-codiscrete (C x)) → ((x : A) → C (unit-♯ x)) → (x : ♯ A) → C x
ind-crisp-ind-♯ {A = A} C is-codiscrete-C f x' =
  crisp-ind-♯
    ( λ X → (x : ♯ X) (p : X ＝ A) → C (tr ♯ p x))
    ( λ x →
      is-codiscrete-Π
        ( λ y → is-codiscrete-Π
          ( λ p → is-codiscrete-C (tr ♯ p y))))
    ( λ A' →
      crisp-ind-♯
        ( λ y → (p : A' ＝ A) → C (tr ♯ p y))
        ( λ y → is-codiscrete-Π (λ p → is-codiscrete-C (tr ♯ p y)))
        ( λ x p → tr C (crisp-tr-sharp p) (f (tr id p (crisp-elim-♯ x)))))
    ( A)
    ( x')
    ( refl)
```

The accompanying computation principle remains to be fully formalized.

```text
compute-ind-crisp-ind-♯ :
  {@♭ l1 : Level} {l2 : Level} {A : UU l1} (C : ♯ A → UU l2) →
  (is-codiscrete-C : (x : ♯ A) → is-codiscrete (C x)) →
  (f : (x : A) → C (unit-♯ x)) → (x : A) →
  ind-crisp-ind-♯ C is-codiscrete-C f (unit-♯ x) ＝ f x
compute-ind-crisp-ind-♯ {A = A} C is-codiscrete-C f x =
  crisp-ind-♯
    ( λ X → (x : X) (p : X ＝ A) →
      ind-crisp-ind-♯ {!   !} {!   !} {!   !} {!   !})
    ( {!   !})
    {!   !}
    ( A)
    ( x)
    ( refl)
```

### Flat after sharp

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-♭-elim-♯ : ♭ (♯ A) → ♭ A
  ap-♭-elim-♯ = crisp-ap-♭ crisp-elim-♯

  ap-♭-unit-♯ : ♭ A → ♭ (♯ A)
  ap-♭-unit-♯ = ap-♭ unit-♯

  is-section-ap-♭-unit-♯ : ap-♭-elim-♯ ∘ ap-♭-unit-♯ ~ id
  is-section-ap-♭-unit-♯ (cons-♭ x) =
    crisp-ap cons-♭ (compute-crisp-elim-♯ x)

  is-retraction-ap-♭-unit-♯ : ap-♭-unit-♯ ∘ ap-♭-elim-♯ ~ id
  is-retraction-ap-♭-unit-♯ (cons-♭ x) =
    crisp-ap cons-♭ (uniqueness-crisp-elim-♯ x)

  is-equiv-ap-♭-elim-♯ : is-equiv ap-♭-elim-♯
  pr1 (pr1 is-equiv-ap-♭-elim-♯) = ap-♭-unit-♯
  pr2 (pr1 is-equiv-ap-♭-elim-♯) = is-section-ap-♭-unit-♯
  pr1 (pr2 is-equiv-ap-♭-elim-♯) = ap-♭-unit-♯
  pr2 (pr2 is-equiv-ap-♭-elim-♯) = is-retraction-ap-♭-unit-♯

  equiv-ap-♭-elim-♯ : ♭ (♯ A) ≃ ♭ A
  pr1 equiv-ap-♭-elim-♯ = ap-♭-elim-♯
  pr2 equiv-ap-♭-elim-♯ = is-equiv-ap-♭-elim-♯

  is-equiv-ap-♭-unit-♯ : is-equiv ap-♭-unit-♯
  pr1 (pr1 is-equiv-ap-♭-unit-♯) = ap-♭-elim-♯
  pr2 (pr1 is-equiv-ap-♭-unit-♯) = is-retraction-ap-♭-unit-♯
  pr1 (pr2 is-equiv-ap-♭-unit-♯) = ap-♭-elim-♯
  pr2 (pr2 is-equiv-ap-♭-unit-♯) = is-section-ap-♭-unit-♯

  equiv-ap-♭-unit-♯ : ♭ A ≃ ♭ (♯ A)
  pr1 equiv-ap-♭-unit-♯ = ap-♭-unit-♯
  pr2 equiv-ap-♭-unit-♯ = is-equiv-ap-♭-unit-♯
```

### Sharp after flat

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  ap-♯-counit-♭ : ♯ (♭ A) → ♯ A
  ap-♯-counit-♭ = rec-♯ (unit-♯ ∘ counit-♭)

  ap-♯-cons-♭ : ♯ A → ♯ (♭ A)
  ap-♯-cons-♭ =
    rec-♯
      ( crisp-rec-♯
        ( ♯ (♭ A))
        ( is-codiscrete-♯ (♭ A))
        ( λ x → unit-♯ (cons-♭ x)))
```

It remains to show that these two are inverses to eachother.

```text
  is-section-cons-♭ : ap-♯-counit-♭ ∘ cons-♭ ~ id
  is-section-cons-♭ =
    ind-subuniverse-♯
      ( A)
      ( λ x → ap-♯-counit-♭ (cons-♭ x) ＝ x)
      ( λ x → is-codiscrete-Id-♯ (ap-♯-counit-♭ (cons-♭ x)) x)
      ( λ x →
          crisp-rec-♯
            ( ap-♯-counit-♭ (cons-♭ (unit-♯ x)) ＝ unit-♯ x)
            ( is-codiscrete-Id-♯ (ap-♯-counit-♭ (cons-♭ (unit-♯ x))) (unit-♯ x))
            ( λ y →
              compute-rec-subuniverse-♯
                {!   !} (♯ A) {!  is-codiscrete-♯ ?  !} {!   !} {!   !})
            {!   !})
```

### Sharp is uniquely eliminating

This remains to be formalized.

```text
map-crisp-retraction-precomp-unit-♯ :
  {l1 : Level} {l2 : Level} {X : UU l1} {P : ♯ X → UU l2} →
  ((x : ♯ X) → ♯ (P x)) → (x : X) → ♯ (P (unit-♯ x))
map-crisp-retraction-precomp-unit-♯ {P = P} f = {!   !}

crisp-elim-♯' :
    {@♭ l : Level} {@♭ A : UU l} → @♭ ♯ A → A
crisp-elim-♯' {A = A} x = crisp-ind-♯ {!   !} {!   !} {!   !} {!   !}

is-retraction-map-crisp-retraction-precomp-unit-♯ :
  {@♭ l1 : Level} {l2 : Level} {@♭ X : UU l1} {P : ♯ X → UU l2} →
  map-crisp-retraction-precomp-unit-♯ {X = X} {P} ∘ {! precomp-Π (unit-♯) (♯ ∘ P)  !} ~ id
is-retraction-map-crisp-retraction-precomp-unit-♯ = {!   !}

is-uniquely-eliminating-♯ :
  {l : Level} → is-uniquely-eliminating-modality (unit-♯ {l})
is-uniquely-eliminating-♯ X P .pr1 =
  section-multivariable-section 2 (precomp-Π unit-♯ (♯ ∘ P)) (induction-principle-♯ X P)
is-uniquely-eliminating-♯ {l} X P .pr2 .pr1 x =
is-uniquely-eliminating-♯ X P .pr2 .pr2 f =
  eq-htpy
  ( λ x →
    equational-reasoning
      {!   !}
      ＝ {!   !} by {!   !}
      ＝ {!   !} by compute-crisp-ind-♯ (♯ ∘ P) {! is-codiscrete-♯ ∘ P  !} crisp-elim-♯ {! f !}
      ＝ {!   !} by {!   !})
```

## See also

- In [codiscrete types](modal-type-theory.codiscrete-types.md), we postulate
  that the sharp modality is a
  [higher modality](orthogonal-factorization-systems.higher-modalities.md).

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
