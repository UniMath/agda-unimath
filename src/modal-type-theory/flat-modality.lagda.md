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

### Crisp assumptions are weaker

```agda
crispen :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {P : A → UU l2} →
  ((x : A) → P x) → ((@♭ x : A) → P x)
crispen f x = f x
```

## Properties

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

  section-diagonal-flat : section diagonal-flat
  pr1 section-diagonal-flat = map-flat-counit-flat
  pr2 section-diagonal-flat = is-section-flat-counit-flat

  retraction-diagonal-flat : retraction diagonal-flat
  pr1 retraction-diagonal-flat = map-flat-counit-flat
  pr2 retraction-diagonal-flat = is-retraction-flat-counit-flat

  is-equiv-diagonal-flat : is-equiv diagonal-flat
  pr1 is-equiv-diagonal-flat = section-diagonal-flat
  pr2 is-equiv-diagonal-flat = retraction-diagonal-flat

  equiv-diagonal-flat : ♭ A ≃ ♭ (♭ A)
  pr1 equiv-diagonal-flat = diagonal-flat
  pr2 equiv-diagonal-flat = is-equiv-diagonal-flat
```

## See also

- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md) we
  postulate that the flat modality is left adjoint to the
  [sharp modality](modal-type-theory.sharp-modality.md).
- [Flat discrete types](modal-type-theory.flat-discrete-crisp-types.md) for
  types that are flat modal.

## References

- Michael Shulman, _Brouwer's fixed-point theorem in real-cohesive homotopy type
  theory_, 2015 ([arXiv:1509.07584](https://arxiv.org/abs/1509.07584))
- Dan Licata, _cohesion-agda_, GitHub repository
  (<https://github.com/dlicata335/cohesion-agda>)
