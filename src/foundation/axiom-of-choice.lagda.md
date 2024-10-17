# The axiom of choice

```agda
module foundation.axiom-of-choice where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-propositional-truncation
open import foundation.inhabited-types
open import foundation.postcomposition-functions
open import foundation.projective-types
open import foundation.propositional-truncations
open import foundation.sections
open import foundation.split-surjective-maps
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.precomposition-functions
open import foundation-core.sets
```

</details>

## Idea

The {{#concept "axiom of choice" WD="axiom of choice" WDID=Q179692 Agda=AC-0}}
asserts that for every family of [inhabited](foundation.inhabited-types.md)
types `B` indexed by a [set](foundation-core.sets.md) `A`, the type of sections
of that family `(x : A) → B x` is inhabited.

## Definition

### The axiom of choice restricted to sets

```agda
AC-Set : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC-Set l1 l2 =
  (A : Set l1) (B : type-Set A → Set l2) →
  ((x : type-Set A) → is-inhabited (type-Set (B x))) →
  is-inhabited ((x : type-Set A) → type-Set (B x))
```

### The axiom of choice

```agda
AC-0 : (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
AC-0 l1 l2 =
  (A : Set l1) (B : type-Set A → UU l2) →
  ((x : type-Set A) → is-inhabited (B x)) →
  is-inhabited ((x : type-Set A) → B x)
```

## Properties

### Every type is set-projective if and only if the axiom of choice holds

```agda
is-set-projective-AC-0 :
  {l1 l2 l3 : Level} → AC-0 l2 (l1 ⊔ l2) →
  (X : UU l3) → is-set-projective l1 l2 X
is-set-projective-AC-0 ac X A B f h =
  map-trunc-Prop
    ( ( map-Σ
        ( λ g → ((map-surjection f) ∘ g) ＝ h)
        ( precomp h A)
        ( λ s H → htpy-postcomp X H h)) ∘
      ( section-is-split-surjective (map-surjection f)))
    ( ac B (fiber (map-surjection f)) (is-surjective-map-surjection f))

AC-0-is-set-projective :
  {l1 l2 : Level} →
  ({l : Level} (X : UU l) → is-set-projective (l1 ⊔ l2) l1 X) →
  AC-0 l1 l2
AC-0-is-set-projective H A B K =
  map-trunc-Prop
    ( map-equiv (equiv-Π-section-pr1 {B = B}) ∘ tot (λ g → htpy-eq))
    ( H ( type-Set A)
        ( Σ (type-Set A) B)
        ( A)
        ( pr1 , (λ a → map-trunc-Prop (map-inv-fiber-pr1 B a) (K a)))
        ( id))
```
