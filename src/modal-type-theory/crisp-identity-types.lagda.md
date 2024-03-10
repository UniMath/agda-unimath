# Crisp identity types

```agda
{-# OPTIONS --cohesion --flat-split #-}

module modal-type-theory.crisp-identity-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.retractions
open import foundation.retracts-of-types
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.universe-levels

open import modal-type-theory.flat-modality
```

</details>

## Idea

We record here some basic facts about
[identity types](foundation-core.identity-types.md) in crisp contexts.

## Definitions

### Crisp identification induction

```agda
weak-crisp-ind-Id :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {@♭ a : A} →
  (C : (@♭ y : A) → (a ＝ y) → UU l2) →
  C a refl →
  (@♭ y : A) (@♭ p : a ＝ y) → C y p
weak-crisp-ind-Id C b _ refl = b

-- TODO: this is how the principle is stated in Shu15. It can be proved with `pointwise-sharp` (except for any cohesive universe level)
module _
  {@♭ l1 l2 : Level} {@♭ A : UU l1}
  (@♭ C : (@♭ x y : A) → @♭ (x ＝ y) → UU l2)
  (@♭ d : ((@♭ x : A) → C x x refl))
  where

  postulate
    crisp-ind-Id : {@♭ x y : A} (@♭ p : x ＝ y) → C x y p

    compute-crisp-ind-Id : (@♭ x : A) → crisp-ind-Id {x} refl ＝ d x
```

### Crisp action on identifications

```agda
crisp-ap :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} {B : UU l2} {@♭ x y : A}
  (f : @♭ A → B) → @♭ (x ＝ y) → f x ＝ f y
crisp-ap f refl = refl
```

### Crisp transport along identifications

```agda
crisp-tr :
  {@♭ l1 : Level} {l2 : Level} {@♭ A : UU l1} (B : A → UU l2)
  {@♭ x y : A} (@♭ p : x ＝ y) → B x → B y
crisp-tr B refl x = x
```

## Properties

### Characterizing equality in the image of the flat modality

```agda
module _
  {@♭ l : Level} {@♭ A : UU l}
  where

  Eq-flat : ♭ A → ♭ A → UU l
  Eq-flat (cons-flat x) (cons-flat y) = ♭ (x ＝ y)

  refl-Eq-flat : (u : ♭ A) → Eq-flat u u
  refl-Eq-flat (cons-flat x) = cons-flat refl

  Eq-eq-flat : (u v : ♭ A) → u ＝ v → Eq-flat u v
  Eq-eq-flat u .u refl = refl-Eq-flat u

  eq-Eq-flat : (u v : ♭ A) → Eq-flat u v → u ＝ v
  eq-Eq-flat (cons-flat x) (cons-flat .x) (cons-flat refl) = refl
```

The retraction part is easy:

```agda
  is-retraction-eq-Eq-flat :
    (u v : ♭ A) → is-retraction (Eq-eq-flat u v) (eq-Eq-flat u v)
  is-retraction-eq-Eq-flat (cons-flat x) (cons-flat .x) refl = refl

  retraction-Eq-eq-flat : (u v : ♭ A) → retraction (Eq-eq-flat u v)
  pr1 (retraction-Eq-eq-flat u v) = eq-Eq-flat u v
  pr2 (retraction-Eq-eq-flat u v) = is-retraction-eq-Eq-flat u v

  retract-Eq-flat :
    (u v : ♭ A) → (u ＝ v) retract-of (Eq-flat u v)
  pr1 (retract-Eq-flat u v) = Eq-eq-flat u v
  pr1 (pr2 (retract-Eq-flat u v)) = eq-Eq-flat u v
  pr2 (pr2 (retract-Eq-flat u v)) = is-retraction-eq-Eq-flat u v

  is-injective-eq-Eq-flat :
    (u v : ♭ A) → is-injective (Eq-eq-flat u v)
  is-injective-eq-Eq-flat u v =
    is-injective-retraction (Eq-eq-flat u v) (retraction-Eq-eq-flat u v)
```

To show it is also a section, however, we need the stronger crisp identity
induction principle, which we have only postulated so far.

```agda
  is-section-eq-Eq-flat :
    (u v : ♭ A) → is-section (Eq-eq-flat u v) (eq-Eq-flat u v)
  is-section-eq-Eq-flat (cons-flat x) (cons-flat y) (cons-flat p) =
    crisp-ind-Id
      ( λ x y p →
        ( Eq-eq-flat
          ( cons-flat x)
          ( cons-flat y)
          ( eq-Eq-flat (cons-flat x) (cons-flat y) (cons-flat p))) ＝
        ( cons-flat p))
      ( λ _ → refl)
      ( p)
```

```agda
  abstract
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

The following is Theorem 6.1 in {{#cite Shu17}}.

```agda
  crisp-extensionality-flat :
    (@♭ x y : A) → (cons-flat x ＝ cons-flat y) ≃ ♭ (x ＝ y)
  crisp-extensionality-flat x y =
    extensionality-flat (cons-flat x) (cons-flat y)
```

The following is Corollary 6.2 in {{#cite Shu17}}.

```agda
  crisp-flat-extensionality-flat :
    (@♭ u v : ♭ A) → (u ＝ v) ≃ ♭ (counit-flat u ＝ counit-flat v)
  crisp-flat-extensionality-flat (cons-flat x) (cons-flat y) =
    extensionality-flat (cons-flat x) (cons-flat y)
```
