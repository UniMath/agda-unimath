# The flat modality

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.flat-modality where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
```

</details>

## Idea

The {{#concept "flat modality" Agda=♭}} is an axiomatized comonadic modality we
adjoin to our type theory by use of _crisp type theory_.

## Definition

### The flat operator on types

```agda
data ♭ {@♭ l : Level} (@♭ A : UU l) : UU l where
  intro-flat : @♭ A → ♭ A

flat : {@♭ l : Level} (@♭ A : UU l) → UU l
flat = ♭
```

### The flat counit

```agda
counit-flat : {@♭ l : Level} {@♭ A : UU l} → ♭ A → A
counit-flat (intro-flat x) = x
```

### Flat dependent elimination

```agda
ind-flat :
  {@♭ l1 : Level} {@♭ A : UU l1} {l2 : Level} (C : ♭ A → UU l2) →
  ((@♭ u : A) → C (intro-flat u)) →
  (x : ♭ A) → C x
ind-flat C f (intro-flat x) = f x
```

### Flat elimination

```agda
rec-flat :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {C : UU l2} →
  (@♭ A → C) → ♭ A → C
rec-flat {C = C} = ind-flat (λ _ → C)
```

### Crispening statements

```agda
crispen :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {P : A → UU l2} →
  ((x : A) → P x) → ((@♭ x : A) → P x)
crispen f x = f x
```

### The associated family over `♭ A` to a type family defined on crisp elements of `A`

```agda
family-over-flat :
  {@♭ l1 l2 : Level} {@♭ A : UU l1} (@♭ P : @♭ A → UU l2) → ♭ A → UU l2
family-over-flat P (intro-flat x) = P x
```

## Properties

### The flat modality is idempotent

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  is-crisp-section-intro-flat : (@♭ x : A) → counit-flat (intro-flat x) ＝ x
  is-crisp-section-intro-flat _ = refl

  is-crisp-retraction-intro-flat : (@♭ x : ♭ A) → intro-flat (counit-flat x) ＝ x
  is-crisp-retraction-intro-flat (intro-flat _) = refl
```

#### The equivalence `♭ A ≃ ♭ (♭ A)`

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  diagonal-flat : ♭ A → ♭ (♭ A)
  diagonal-flat (intro-flat x) = intro-flat (intro-flat x)

  is-retraction-diagonal-flat : is-retraction counit-flat diagonal-flat
  is-retraction-diagonal-flat (intro-flat (intro-flat _)) = refl

  is-section-diagonal-flat : is-section counit-flat diagonal-flat
  is-section-diagonal-flat (intro-flat _) = refl

  section-diagonal-flat : section diagonal-flat
  pr1 section-diagonal-flat = counit-flat
  pr2 section-diagonal-flat = is-retraction-diagonal-flat

  retraction-diagonal-flat : retraction diagonal-flat
  pr1 retraction-diagonal-flat = counit-flat
  pr2 retraction-diagonal-flat = is-section-diagonal-flat

  abstract
    is-equiv-diagonal-flat : is-equiv diagonal-flat
    pr1 is-equiv-diagonal-flat = section-diagonal-flat
    pr2 is-equiv-diagonal-flat = retraction-diagonal-flat

  equiv-diagonal-flat : ♭ A ≃ ♭ (♭ A)
  pr1 equiv-diagonal-flat = diagonal-flat
  pr2 equiv-diagonal-flat = is-equiv-diagonal-flat
```

#### The equivalence `♭ (♭ A) ≃ ♭ A`

```agda
  section-flat-counit-flat : section (counit-flat {A = ♭ A})
  pr1 section-flat-counit-flat = diagonal-flat
  pr2 section-flat-counit-flat = is-section-diagonal-flat

  retraction-flat-counit-flat : retraction (counit-flat {A = ♭ A})
  pr1 retraction-flat-counit-flat = diagonal-flat
  pr2 retraction-flat-counit-flat = is-retraction-diagonal-flat

  abstract
    is-equiv-flat-counit-flat : is-equiv (counit-flat {A = ♭ A})
    pr1 is-equiv-flat-counit-flat = section-flat-counit-flat
    pr2 is-equiv-flat-counit-flat = retraction-flat-counit-flat

  equiv-flat-counit-flat : ♭ (♭ A) ≃ ♭ A
  equiv-flat-counit-flat = inv-equiv equiv-diagonal-flat
```

## See also

- In [the flat-sharp adjunction](modal-type-theory.flat-sharp-adjunction.md) we
  postulate that the flat modality is left adjoint to the
  [sharp modality](modal-type-theory.sharp-modality.md).
- [Flat discrete crisp types](modal-type-theory.flat-discrete-crisp-types.md)
  for crisp types that are flat modal.

## References

{{#bibliography}} {{#reference Shu18}} {{#reference Dlicata335/Cohesion-Agda}}

## External links

- [Flat Modality](https://agda.readthedocs.io/en/latest/language/flat.html) on
  the Agda documentation pages.
