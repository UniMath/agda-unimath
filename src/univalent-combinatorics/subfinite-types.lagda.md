# Subfinite types

```agda
module univalent-combinatorics.subfinite-types where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.injective-maps
open import foundation.law-of-excluded-middle
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.propositions

open import univalent-combinatorics.finite-types
open import univalent-combinatorics.kuratowsky-finite-sets
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A subfinite type is a set `X` for which there exists an injection into `X` from
a standard finite type. In other words, the subfinite types are the subset of a
standard finite type.

## Definition

```agda
is-subfinite-Prop : {l : Level} → UU l → Prop l
is-subfinite-Prop X =
  exists-structure-Prop ℕ (λ n → injection X (Fin n))

is-subfinite : {l : Level} → UU l → UU l
is-subfinite X = type-Prop (is-subfinite-Prop X)
```

### Subfinite types are sets

```agda
is-set-is-subfinite : {l : Level} {X : UU l} → is-subfinite X → is-set X
is-set-is-subfinite {X = X} =
  elim-exists
    ( is-set-Prop X)
    ( λ n (f , is-inj) → is-set-is-injective (is-set-Fin n) is-inj)

Set-is-subfinite : {l : Level} {X : UU l} → is-subfinite X → Set l
Set-is-subfinite {X = X} is-sub = X , is-set-is-subfinite is-sub
```

### Subfinite sets are closed under injections

```agda
is-subfinite-injection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  injection X Y →
  is-subfinite Y →
  is-subfinite X
is-subfinite-injection {X = X} f =
  elim-exists
    ( is-subfinite-Prop X)
    ( λ n g → intro-exists n (comp-injection f g))
```

### Any finite set is subfinite

```agda
is-subfinite-is-finite : {l : Level} {X : UU l} → is-finite X → is-subfinite X
is-subfinite-is-finite {X = X} =
  elim-exists
    ( is-subfinite-Prop X)
    ( λ n e →
      intro-exists n
        ( map-inv-equiv e , λ {_} {_} → is-injective-map-inv-equiv e))
```

### Classical facts

```agda
is-finite-is-subfinite :
  {l : Level} {X : UU l} → LEM l → is-subfinite X → is-finite X
is-finite-is-subfinite {X = X} lem is-sub with lem (is-inhabited-Prop X)
... | inl is-inh =
  elim-exists
    ( is-finite-Prop X)
    ( λ n (f , is-inj) →
      ( apply-universal-property-trunc-Prop
        ( is-inhabited-inv-surjections f is-inj
          ( apply-LEM lem ∘ is-prop-map-is-injective (is-set-Fin n) is-inj)
          ( is-inh))
        ( is-finite-Prop X)
        ( λ g →
          is-finite-is-kuratowsky-finite-set
            ( Set-is-subfinite is-sub)
            ( lem)
            ( intro-exists n g))))
    ( is-sub)
... | inr not-inh = is-finite-is-empty (not-inh ∘ unit-trunc-Prop)

is-finite-injection :
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} →
  LEM l1 →
  injection X Y →
  is-finite Y →
  is-finite X
is-finite-injection lem f =
  is-finite-is-subfinite lem ∘ is-subfinite-injection f ∘ is-subfinite-is-finite
```
