# The flat modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
```

</details>

## Idea

The **flat modality** is an axiomatized comonadic modality we adjoin to our type
theory by use of _crisp type theory_.

## Definition

### The flat operator on types

```agda
data ♭ {@♭ l : Level} (@♭ A : UU l) : UU l where
  con-♭ : @♭ A → ♭ A
```

### The flat counit

```agda
counit-crisp : {@♭ l : Level} {@♭ A : UU l} → @♭ A → A
counit-crisp x = x

counit-♭ : {@♭ l : Level} {@♭ A : UU l} → ♭ A → A
counit-♭ (con-♭ x) = counit-crisp x
```

### Flat dependent elimination

```agda
ind-♭ :
  {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level} (C : ♭ A → UU l2) →
  ((@♭ u : A) → C (con-♭ u)) →
  (x : ♭ A) → C x
ind-♭ C f (con-♭ x) = f x

crisp-ind-♭ :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : @♭ ♭ A → UU l2) →
  ((@♭ u : A) → C (con-♭ u)) → (@♭ x : ♭ A) → C x
crisp-ind-♭ C f (con-♭ x) = f x
```

### Flat elimination

```agda
rec-♭ :
  {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level} (C : UU l2) →
  ((@♭ u : A) → C) → (x : ♭ A) → C
rec-♭ C = ind-♭ (λ _ → C)

crisp-rec-♭ :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : UU l2) →
  ((@♭ u : A) → C) → (@♭ x : ♭ A) → C
crisp-rec-♭ C = crisp-ind-♭ (λ _ → C)
```

### Flat action on maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  ap-♭ : @♭ (A → B) → (♭ A → ♭ B)
  ap-♭ f (con-♭ x) = con-♭ (f x)

  crisp-ap-♭ : @♭ (@♭ A → B) → (♭ A → ♭ B)
  crisp-ap-♭ f (con-♭ x) = con-♭ (f x)

  coap-♭ : (♭ A → ♭ B) → (@♭ A → B)
  coap-♭ f x = counit-♭ (f (con-♭ x))

  is-crisp-retraction-coap-♭ : (@♭ f : @♭ A → B) → coap-♭ (crisp-ap-♭ f) ＝ f
  is-crisp-retraction-coap-♭ _ = refl
```

## Properties

### Crisp assumptions are weaker

```agda
crispen :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {P : A → UU l2} →
  ((x : A) → P x) → ((@♭ x : A) → P x)
crispen f x = f x
```

### The flat modality is idempotent

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-crisp-section-con-♭ : (@♭ x : A) → counit-♭ (con-♭ x) ＝ x
  is-crisp-section-con-♭ _ = refl

  is-crisp-retraction-con-♭ : (@♭ x : ♭ A) → con-♭ (counit-♭ x) ＝ x
  is-crisp-retraction-con-♭ (con-♭ _) = refl
```

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  map-♭-counit-♭ : ♭ (♭ A) → ♭ A
  map-♭-counit-♭ (con-♭ x) = x

  diag-♭ : ♭ A → ♭ (♭ A)
  diag-♭ (con-♭ x) = con-♭ (con-♭ x)

  is-section-♭-counit-♭ :
    (diag-♭ ∘ map-♭-counit-♭) ~ id
  is-section-♭-counit-♭ (con-♭ (con-♭ _)) = refl

  is-retraction-♭-counit-♭ :
    (map-♭-counit-♭ ∘ diag-♭) ~ id
  is-retraction-♭-counit-♭ (con-♭ _) = refl

  section-♭-counit-♭ : section map-♭-counit-♭
  pr1 section-♭-counit-♭ = diag-♭
  pr2 section-♭-counit-♭ = is-retraction-♭-counit-♭

  retraction-♭-counit-♭ : retraction map-♭-counit-♭
  pr1 retraction-♭-counit-♭ = diag-♭
  pr2 retraction-♭-counit-♭ = is-section-♭-counit-♭

  is-equiv-♭-counit-♭ : is-equiv map-♭-counit-♭
  pr1 is-equiv-♭-counit-♭ = section-♭-counit-♭
  pr2 is-equiv-♭-counit-♭ = retraction-♭-counit-♭

  equiv-♭-counit-♭ : ♭ (♭ A) ≃ ♭ A
  pr1 equiv-♭-counit-♭ = map-♭-counit-♭
  pr2 equiv-♭-counit-♭ = is-equiv-♭-counit-♭

  inv-equiv-♭-counit-♭ : ♭ A ≃ ♭ (♭ A)
  inv-equiv-♭-counit-♭ = inv-equiv equiv-♭-counit-♭
```

### Flat distributes over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-crisp-distributive-♭-Π : ♭ ((x : A) → B x) → ((@♭ x : A) → ♭ (B x))
  map-crisp-distributive-♭-Π (con-♭ f) x = con-♭ (f x)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-crisp-distributive-♭-function-types : ♭ (A → B) → (@♭ A → ♭ B)
  map-crisp-distributive-♭-function-types = map-crisp-distributive-♭-Π

  map-distributive-♭-function-types : ♭ (A → B) → (♭ A → ♭ B)
  map-distributive-♭-function-types f (con-♭ x) =
    map-crisp-distributive-♭-function-types f x
```

### Flat distributes over Σ-types

```agda
Σ♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : A → UU l2) → UU (l1 ⊔ l2)
Σ♭ A B = Σ (♭ A) (λ {(con-♭ x) → ♭ (B x)})

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-♭-Σ : ♭ (Σ A B) → Σ♭ A B
  pr1 (map-distributive-♭-Σ (con-♭ (x , y))) = con-♭ x
  pr2 (map-distributive-♭-Σ (con-♭ (x , y))) = con-♭ y

  map-inv-distributive-♭-Σ : Σ♭ A B → ♭ (Σ A B)
  map-inv-distributive-♭-Σ (con-♭ x , con-♭ y) = con-♭ (x , y)

  is-section-distributive-♭-Σ :
    (map-inv-distributive-♭-Σ ∘ map-distributive-♭-Σ) ~ id
  is-section-distributive-♭-Σ (con-♭ _) = refl

  is-retraction-distributive-♭-Σ :
    (map-distributive-♭-Σ ∘ map-inv-distributive-♭-Σ) ~ id
  is-retraction-distributive-♭-Σ (con-♭ _ , con-♭ _) = refl

  section-distributive-♭-Σ : section map-distributive-♭-Σ
  pr1 section-distributive-♭-Σ = map-inv-distributive-♭-Σ
  pr2 section-distributive-♭-Σ = is-retraction-distributive-♭-Σ

  retraction-distributive-♭-Σ : retraction map-distributive-♭-Σ
  pr1 retraction-distributive-♭-Σ = map-inv-distributive-♭-Σ
  pr2 retraction-distributive-♭-Σ = is-section-distributive-♭-Σ

  is-equiv-distributive-♭-Σ : is-equiv map-distributive-♭-Σ
  pr1 is-equiv-distributive-♭-Σ = section-distributive-♭-Σ
  pr2 is-equiv-distributive-♭-Σ = retraction-distributive-♭-Σ

  equiv-distributive-♭-Σ : ♭ (Σ A B) ≃ Σ♭ A B
  pr1 equiv-distributive-♭-Σ = map-distributive-♭-Σ
  pr2 equiv-distributive-♭-Σ = is-equiv-distributive-♭-Σ

  inv-equiv-distributive-♭-Σ : Σ♭ A B ≃ ♭ (Σ A B)
  inv-equiv-distributive-♭-Σ = inv-equiv equiv-distributive-♭-Σ
```

## See also

- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md) we
  postulate that the flat modality is left adjoint to the
  [sharp modality](modal-type-theory.sharp-modality.md).
- [Flat types](modal-type-theory.flat-types.md) for types that are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
