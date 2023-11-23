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
  cons-flat : @♭ A → ♭ A
```

### The flat counit

```agda
counit-crisp : {@♭ l : Level} {@♭ A : UU l} → @♭ A → A
counit-crisp x = x

counit-flat : {@♭ l : Level} {@♭ A : UU l} → ♭ A → A
counit-flat (cons-flat x) = counit-crisp x
```

### Flat dependent elimination

```agda
ind-flat :
  {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level} (C : ♭ A → UU l2) →
  ((@♭ u : A) → C (cons-flat u)) →
  (x : ♭ A) → C x
ind-flat C f (cons-flat x) = f x

crisp-ind-flat :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : @♭ ♭ A → UU l2) →
  ((@♭ u : A) → C (cons-flat u)) → (@♭ x : ♭ A) → C x
crisp-ind-flat C f (cons-flat x) = f x
```

### Flat elimination

```agda
rec-flat :
  {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level} (C : UU l2) →
  ((@♭ u : A) → C) → (x : ♭ A) → C
rec-flat C = ind-flat (λ _ → C)

crisp-rec-flat :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (C : UU l2) →
  ((@♭ u : A) → C) → (@♭ x : ♭ A) → C
crisp-rec-flat C = crisp-ind-flat (λ _ → C)
```

### Flat action on maps

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  ap-flat : @♭ (A → B) → (♭ A → ♭ B)
  ap-flat f (cons-flat x) = cons-flat (f x)

  ap-crisp-flat : @♭ (@♭ A → B) → (♭ A → ♭ B)
  ap-crisp-flat f (cons-flat x) = cons-flat (f x)

  coap-flat : (♭ A → ♭ B) → (@♭ A → B)
  coap-flat f x = counit-flat (f (cons-flat x))

  is-crisp-retraction-coap-flat :
    (@♭ f : @♭ A → B) → coap-flat (ap-crisp-flat f) ＝ f
  is-crisp-retraction-coap-flat _ = refl
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

  is-crisp-section-cons-flat : (@♭ x : A) → counit-flat (cons-flat x) ＝ x
  is-crisp-section-cons-flat _ = refl

  is-crisp-retraction-cons-flat : (@♭ x : ♭ A) → cons-flat (counit-flat x) ＝ x
  is-crisp-retraction-cons-flat (cons-flat _) = refl
```

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  map-flat-counit-flat : ♭ (♭ A) → ♭ A
  map-flat-counit-flat (cons-flat x) = x

  diagonal-flat : ♭ A → ♭ (♭ A)
  diagonal-flat (cons-flat x) = cons-flat (cons-flat x)

  is-section-flat-counit-flat :
    diagonal-flat ∘ map-flat-counit-flat ~ id
  is-section-flat-counit-flat (cons-flat (cons-flat _)) = refl

  is-retraction-flat-counit-flat :
    map-flat-counit-flat ∘ diagonal-flat ~ id
  is-retraction-flat-counit-flat (cons-flat _) = refl

  section-flat-counit-flat : section map-flat-counit-flat
  pr1 section-flat-counit-flat = diagonal-flat
  pr2 section-flat-counit-flat = is-retraction-flat-counit-flat

  retraction-flat-counit-flat : retraction map-flat-counit-flat
  pr1 retraction-flat-counit-flat = diagonal-flat
  pr2 retraction-flat-counit-flat = is-section-flat-counit-flat

  is-equiv-flat-counit-flat : is-equiv map-flat-counit-flat
  pr1 is-equiv-flat-counit-flat = section-flat-counit-flat
  pr2 is-equiv-flat-counit-flat = retraction-flat-counit-flat

  equiv-flat-counit-flat : ♭ (♭ A) ≃ ♭ A
  pr1 equiv-flat-counit-flat = map-flat-counit-flat
  pr2 equiv-flat-counit-flat = is-equiv-flat-counit-flat

  inv-equiv-flat-counit-flat : ♭ A ≃ ♭ (♭ A)
  inv-equiv-flat-counit-flat = inv-equiv equiv-flat-counit-flat
```

### Flat distributes over dependent function types

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-crisp-distributive-flat-Π : ♭ ((x : A) → B x) → ((@♭ x : A) → ♭ (B x))
  map-crisp-distributive-flat-Π (cons-flat f) x = cons-flat (f x)

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : UU l2}
  where

  map-crisp-distributive-flat-function-types : ♭ (A → B) → (@♭ A → ♭ B)
  map-crisp-distributive-flat-function-types = map-crisp-distributive-flat-Π

  map-distributive-flat-function-types : ♭ (A → B) → (♭ A → ♭ B)
  map-distributive-flat-function-types f (cons-flat x) =
    map-crisp-distributive-flat-function-types f x
```

### Flat distributes over Σ-types

```agda
Σ-♭ : {@♭ l1 l2 : Level} (@♭ A : UU l1) (@♭ B : A → UU l2) → UU (l1 ⊔ l2)
Σ-♭ A B = Σ (♭ A) (λ {(cons-flat x) → ♭ (B x)})

module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ B : A → UU l2}
  where

  map-distributive-flat-Σ : ♭ (Σ A B) → Σ-♭ A B
  pr1 (map-distributive-flat-Σ (cons-flat (x , y))) = cons-flat x
  pr2 (map-distributive-flat-Σ (cons-flat (x , y))) = cons-flat y

  map-inv-distributive-flat-Σ : Σ-♭ A B → ♭ (Σ A B)
  map-inv-distributive-flat-Σ (cons-flat x , cons-flat y) = cons-flat (x , y)

  is-section-distributive-flat-Σ :
    (map-inv-distributive-flat-Σ ∘ map-distributive-flat-Σ) ~ id
  is-section-distributive-flat-Σ (cons-flat _) = refl

  is-retraction-distributive-flat-Σ :
    (map-distributive-flat-Σ ∘ map-inv-distributive-flat-Σ) ~ id
  is-retraction-distributive-flat-Σ (cons-flat _ , cons-flat _) = refl

  section-distributive-flat-Σ : section map-distributive-flat-Σ
  pr1 section-distributive-flat-Σ = map-inv-distributive-flat-Σ
  pr2 section-distributive-flat-Σ = is-retraction-distributive-flat-Σ

  retraction-distributive-flat-Σ : retraction map-distributive-flat-Σ
  pr1 retraction-distributive-flat-Σ = map-inv-distributive-flat-Σ
  pr2 retraction-distributive-flat-Σ = is-section-distributive-flat-Σ

  is-equiv-distributive-flat-Σ : is-equiv map-distributive-flat-Σ
  pr1 is-equiv-distributive-flat-Σ = section-distributive-flat-Σ
  pr2 is-equiv-distributive-flat-Σ = retraction-distributive-flat-Σ

  equiv-distributive-flat-Σ : ♭ (Σ A B) ≃ Σ-♭ A B
  pr1 equiv-distributive-flat-Σ = map-distributive-flat-Σ
  pr2 equiv-distributive-flat-Σ = is-equiv-distributive-flat-Σ

  inv-equiv-distributive-flat-Σ : Σ-♭ A B ≃ ♭ (Σ A B)
  inv-equiv-distributive-flat-Σ = inv-equiv equiv-distributive-flat-Σ
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
