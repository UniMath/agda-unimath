# Zero MacNeille real numbers

```agda
module real-numbers.zero-macneille-real-numbers where
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

open import real-numbers.macneille-real-numbers
open import real-numbers.raising-universe-levels-macneille-real-numbers
open import real-numbers.rational-macneille-real-numbers
open import real-numbers.similarity-macneille-real-numbers
```

</details>

## Idea

A [real number](real-numbers.macneille-real-numbers.md) is
{{#concept "zero" Disambiguation="property of a MacNeille real number" WDID=Q204 WD="zero" Agda=is-zero-macneille-ℝ}}
if it is [similar](real-numbers.similarity-real-numbers.md) to
[zero](real-numbers.rational-real-numbers.md).

## Definition

```agda
is-zero-prop-macneille-ℝ : {l : Level} → macneille-ℝ l → Prop l
is-zero-prop-macneille-ℝ x = sim-prop-macneille-ℝ x zero-macneille-ℝ

is-zero-macneille-ℝ : {l : Level} → macneille-ℝ l → UU l
is-zero-macneille-ℝ x = sim-macneille-ℝ x zero-macneille-ℝ
```

## Properties

### A MacNeille real number `x` is zero if and only if it equals `raise-zero-macneille-ℝ l` for the appropriate universe level `l`

```agda
abstract opaque
  unfolding macneille-real-ℚ

  eq-raise-zero-macneille-ℝ :
    {l : Level} →
    raise-zero-macneille-ℝ l ＝ raise-macneille-ℝ l zero-macneille-ℝ
  eq-raise-zero-macneille-ℝ {l} =
    eq-eq-lower-real-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-ℝ l zero-macneille-ℝ)
      ( refl)

abstract
  sim-raise-zero-macneille-ℝ :
    {l : Level} →
    raise-zero-macneille-ℝ l ~ℝₘ zero-macneille-ℝ
  sim-raise-zero-macneille-ℝ {l} =
    transitive-sim-macneille-ℝ
      ( raise-zero-macneille-ℝ l)
      ( raise-macneille-ℝ l zero-macneille-ℝ)
      ( zero-macneille-ℝ)
      ( sim-raise-macneille-ℝ' l zero-macneille-ℝ)
      ( sim-eq-macneille-ℝ eq-raise-zero-macneille-ℝ)

module _
  {l : Level}
  {x : macneille-ℝ l}
  where

  abstract
    is-zero-eq-raise-zero-macneille-ℝ :
      x ＝ raise-zero-macneille-ℝ l → is-zero-macneille-ℝ x
    is-zero-eq-raise-zero-macneille-ℝ x=0 =
      transitive-sim-macneille-ℝ
        ( x)
        ( raise-zero-macneille-ℝ l)
        ( zero-macneille-ℝ)
        ( sim-raise-zero-macneille-ℝ)
        ( sim-eq-macneille-ℝ x=0)

  abstract
    eq-raise-zero-is-zero-macneille-ℝ :
      is-zero-macneille-ℝ x → x ＝ raise-zero-macneille-ℝ l
    eq-raise-zero-is-zero-macneille-ℝ x~0 =
      eq-sim-macneille-ℝ
        ( transitive-sim-macneille-ℝ
          ( x)
          ( zero-macneille-ℝ)
          ( raise-zero-macneille-ℝ l)
          ( symmetric-sim-macneille-ℝ sim-raise-zero-macneille-ℝ)
          ( x~0))

  abstract
    is-zero-iff-eq-raise-zero-macneille-ℝ :
      (is-zero-macneille-ℝ x) ↔ (x ＝ raise-zero-macneille-ℝ l)
    is-zero-iff-eq-raise-zero-macneille-ℝ =
      ( eq-raise-zero-is-zero-macneille-ℝ ,
        is-zero-eq-raise-zero-macneille-ℝ)

is-zero-raise-zero-macneille-ℝ :
  (l : Level) → is-zero-macneille-ℝ (raise-zero-macneille-ℝ l)
is-zero-raise-zero-macneille-ℝ l = is-zero-eq-raise-zero-macneille-ℝ refl
```

### The subtype of zero MacNeille real numbers is a singleton subtype

```agda
abstract
  is-singleton-subtype-is-zero-macneille-ℝ :
    (l : Level) → is-singleton-subtype (is-zero-prop-macneille-ℝ {l})
  is-singleton-subtype-is-zero-macneille-ℝ l =
    ( ( raise-zero-macneille-ℝ l , is-zero-raise-zero-macneille-ℝ l) ,
      λ (x , is-zero-x) →
        eq-type-subtype
          ( is-zero-prop-macneille-ℝ)
          ( inv (eq-raise-zero-is-zero-macneille-ℝ is-zero-x)))
```
