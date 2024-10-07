# Crisp identity types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.universe-levels

open import modal-type-theory.flat-modality
```

</details>

## Idea

We record here some basic facts about
[identity types](foundation-core.identity-types.md) in
[crisp contexts](modal-type-theory.crisp-types.md).

## Definitions

### Weak crisp identification induction

```agda
weak-crisp-based-ind-Id :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {@♭ a : A} →
  (C : (@♭ y : A) → (a ＝ y) → UU l2) →
  C a refl →
  (@♭ y : A) (@♭ p : a ＝ y) → C y p
weak-crisp-based-ind-Id C b _ refl = b
```

### Based crisp identification induction

Below we postulate the
{{#concept "crisp identity induction principle" Agda=crisp-based-ind-Id}} as
introduced in {{#cite Shu18}}. Note that this principle should follow from the
flat modality's relation to the
[sharp modality](modal-type-theory.sharp-modality.md), and the stronger
`pointwise-sharp` construction as considered in {{#cite DavidJaz/Cohesion}}.

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1} {@♭ x : A}
  (@♭ C : (@♭ y : A) → @♭ (x ＝ y) → UU l2)
  (@♭ d : (C x refl))
  where

  postulate
    crisp-based-ind-Id : {@♭ y : A} (@♭ p : x ＝ y) → C y p
    compute-crisp-based-ind-Id : crisp-based-ind-Id {x} refl ＝ d
```

```agda
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  (@♭ C : (@♭ x y : A) → @♭ (x ＝ y) → UU l2)
  (@♭ d : ((@♭ x : A) → C x x refl))
  where

  crisp-ind-Id : {@♭ x y : A} (@♭ p : x ＝ y) → C x y p
  crisp-ind-Id {x} {y} p = crisp-based-ind-Id (λ y p → C x y p) (d x) {y} p

  compute-crisp-ind-Id : (@♭ x : A) → crisp-ind-Id {x} refl ＝ d x
  compute-crisp-ind-Id x = compute-crisp-based-ind-Id (λ y p → C x y p) (d x)
```

## Properties

### Characterizing equality in the image of the flat modality

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  Eq-flat : ♭ A → ♭ A → UU l
  Eq-flat (intro-flat x) (intro-flat y) = ♭ (x ＝ y)

  refl-Eq-flat : (u : ♭ A) → Eq-flat u u
  refl-Eq-flat (intro-flat x) = intro-flat refl

  Eq-eq-flat : (u v : ♭ A) → u ＝ v → Eq-flat u v
  Eq-eq-flat u .u refl = refl-Eq-flat u

  eq-Eq-flat : (u v : ♭ A) → Eq-flat u v → u ＝ v
  eq-Eq-flat (intro-flat x) (intro-flat .x) (intro-flat refl) = refl
```

The retraction part is easy:

```agda
  is-retraction-eq-Eq-flat :
    (u v : ♭ A) → is-retraction (Eq-eq-flat u v) (eq-Eq-flat u v)
  is-retraction-eq-Eq-flat (intro-flat x) (intro-flat .x) refl = refl

  retraction-Eq-eq-flat : (u v : ♭ A) → retraction (Eq-eq-flat u v)
  pr1 (retraction-Eq-eq-flat u v) = eq-Eq-flat u v
  pr2 (retraction-Eq-eq-flat u v) = is-retraction-eq-Eq-flat u v

  retract-Eq-flat :
    (u v : ♭ A) → (u ＝ v) retract-of (Eq-flat u v)
  pr1 (retract-Eq-flat u v) = Eq-eq-flat u v
  pr1 (pr2 (retract-Eq-flat u v)) = eq-Eq-flat u v
  pr2 (pr2 (retract-Eq-flat u v)) = is-retraction-eq-Eq-flat u v

  is-injective-Eq-eq-flat :
    (u v : ♭ A) → is-injective (Eq-eq-flat u v)
  is-injective-Eq-eq-flat u v =
    is-injective-retraction (Eq-eq-flat u v) (retraction-Eq-eq-flat u v)
```

To show it is also a section, however, we need the stronger crisp identity
induction principle, which we have only postulated so far.

```agda
  is-section-eq-Eq-flat :
    (u v : ♭ A) → is-section (Eq-eq-flat u v) (eq-Eq-flat u v)
  is-section-eq-Eq-flat (intro-flat x) (intro-flat y) (intro-flat p) =
    crisp-ind-Id
      ( λ x y p →
        ( Eq-eq-flat
          ( intro-flat x)
          ( intro-flat y)
          ( eq-Eq-flat (intro-flat x) (intro-flat y) (intro-flat p))) ＝
        ( intro-flat p))
      ( λ _ → refl)
      ( p)
```

```agda
  is-equiv-Eq-eq-flat : (u v : ♭ A) → is-equiv (Eq-eq-flat u v)
  is-equiv-Eq-eq-flat u v =
    is-equiv-is-invertible
      ( eq-Eq-flat u v)
      ( is-section-eq-Eq-flat u v)
      ( is-retraction-eq-Eq-flat u v)

  extensionality-flat : (u v : ♭ A) → (u ＝ v) ≃ Eq-flat u v
  pr1 (extensionality-flat u v) = Eq-eq-flat u v
  pr2 (extensionality-flat u v) = is-equiv-Eq-eq-flat u v
```

The following is Theorem 6.1 in {{#cite Shu18}}.

```agda
  crisp-extensionality-flat :
    (@♭ x y : A) → (intro-flat x ＝ intro-flat y) ≃ ♭ (x ＝ y)
  crisp-extensionality-flat x y =
    extensionality-flat (intro-flat x) (intro-flat y)
```

The following is Corollary 6.2 in {{#cite Shu18}}.

```agda
  crisp-flat-extensionality-flat :
    (@♭ u v : ♭ A) → (u ＝ v) ≃ ♭ (counit-flat u ＝ counit-flat v)
  crisp-flat-extensionality-flat (intro-flat x) (intro-flat y) =
    extensionality-flat (intro-flat x) (intro-flat y)
```

## See also

- We show that identity types between crisp elements of flat discrete crisp
  types are flat discrete crisp in
  [`modal-type-theory.flat-discrete-crisp-types`](modal-type-theory.flat-discrete-crisp-types.md).
- [Action on identifications of crisp functions](modal-type-theory.action-on-identifications-crisp-functions.md)
- [Transport along crisp identifications](modal-type-theory.transport-along-crisp-identifications.md)
