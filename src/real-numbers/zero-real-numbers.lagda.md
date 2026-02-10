# Zero real numbers

```agda
module real-numbers.zero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.singleton-subtypes
open import foundation.subtypes
open import foundation.universe-levels

open import real-numbers.dedekind-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "zero" Disambiguation="property of a real number" WDID=Q204 WD="zero" Agda=is-zero-ℝ}}
if it is [similar](real-numbers.similarity-real-numbers.md) to
[zero](real-numbers.rational-real-numbers.md).

## Definition

```agda
is-zero-prop-ℝ : {l : Level} → ℝ l → Prop l
is-zero-prop-ℝ x = sim-prop-ℝ x zero-ℝ

is-zero-ℝ : {l : Level} → ℝ l → UU l
is-zero-ℝ x = sim-ℝ x zero-ℝ
```

## Properties

### A real number `x` is zero if and only if it equals `raise-zero-ℝ l` for the appropriate universe level `l`

```agda
module _
  {l : Level}
  {x : ℝ l}
  where

  abstract
    is-zero-iff-eq-raise-zero-ℝ : (is-zero-ℝ x) ↔ (x ＝ raise-zero-ℝ l)
    is-zero-iff-eq-raise-zero-ℝ =
      ( is-rational-iff-eq-raise-real-ℝ) ∘iff
      ( inv-iff is-rational-iff-sim-rational-ℝ)

    eq-raise-zero-is-zero-ℝ : is-zero-ℝ x → x ＝ raise-zero-ℝ l
    eq-raise-zero-is-zero-ℝ =
      forward-implication is-zero-iff-eq-raise-zero-ℝ

    is-zero-eq-raise-zero-ℝ : x ＝ raise-zero-ℝ l → is-zero-ℝ x
    is-zero-eq-raise-zero-ℝ =
      backward-implication is-zero-iff-eq-raise-zero-ℝ

is-zero-raise-zero-ℝ : (l : Level) → is-zero-ℝ (raise-zero-ℝ l)
is-zero-raise-zero-ℝ l = is-zero-eq-raise-zero-ℝ refl
```

### The subtype of zero real numbers is a singleton subtype

```agda
abstract
  is-singleton-subtype-is-zero-ℝ :
    (l : Level) → is-singleton-subtype (is-zero-prop-ℝ {l})
  is-singleton-subtype-is-zero-ℝ l =
    ( ( raise-zero-ℝ l , is-zero-raise-zero-ℝ l) ,
      λ (x , is-zero-x) →
        eq-type-subtype
          ( is-zero-prop-ℝ)
          ( inv (eq-raise-zero-is-zero-ℝ is-zero-x)))
```
