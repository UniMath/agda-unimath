# Automorphisms

```agda
module foundation.automorphisms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import structured-types.pointed-types
```

</details>

## Idea

An automorphism on a type `A` is an equivalence `A ≃ A`. We will just reuse the
infrastructure of equivalences for automorphisms.

## Definitions

### The type of automorphisms on a type

```agda
Aut : {l : Level} → UU l → UU l
Aut Y = Y ≃ Y

is-set-Aut : {l : Level} {A : UU l} → is-set A → is-set (Aut A)
is-set-Aut H = is-set-equiv-is-set H H

Aut-Set : {l : Level} → Set l → Set l
pr1 (Aut-Set A) = Aut (type-Set A)
pr2 (Aut-Set A) = is-set-Aut (is-set-type-Set A)

Aut-Pointed-Type : {l : Level} → UU l → Pointed-Type l
pr1 (Aut-Pointed-Type A) = Aut A
pr2 (Aut-Pointed-Type A) = id-equiv
```

### Conjugations of automorphisms

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y)
  where

  map-conjugation-aut :
    Aut X → Aut Y
  map-conjugation-aut f =
    e ∘e f ∘e inv-equiv e

  is-equiv-conjugation-aut :
    is-equiv map-conjugation-aut
  is-equiv-conjugation-aut =
    is-equiv-comp
      ( e ∘e_)
      ( _∘e inv-equiv e)
      ( is-equiv-precomp-equiv-equiv (inv-equiv e))
      ( is-equiv-postcomp-equiv-equiv e)

  conjugation-aut :
    Aut X ≃ Aut Y
  pr1 conjugation-aut = map-conjugation-aut
  pr2 conjugation-aut = is-equiv-conjugation-aut

  map-conjugation-aut' :
    Aut Y → Aut X
  map-conjugation-aut' f =
    inv-equiv e ∘e f ∘e e

  is-equiv-conjugation-aut' :
    is-equiv map-conjugation-aut'
  is-equiv-conjugation-aut' =
    is-equiv-comp
      ( inv-equiv e ∘e_)
      ( _∘e e)
      ( is-equiv-precomp-equiv-equiv e)
      ( is-equiv-postcomp-equiv-equiv (inv-equiv e))

  conjugation-aut' :
    Aut Y ≃ Aut X
  pr1 conjugation-aut' = map-conjugation-aut'
  pr2 conjugation-aut' = is-equiv-conjugation-aut'
```

## Properties

### If `f : Aut X` and `f x ＝ x'`, and `e : X ≃ Y` satisfies `e x ＝ y` and `e x' ＝ y'`, then `(e ∘ f ∘ e⁻¹) y ＝ y'`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (f : Aut X)
  where

  compute-value-conjugation-aut :
    (x : X) {x' : X} {y y' : Y}
    (q : map-equiv e x ＝ y) (q' : map-equiv e x' ＝ y') →
    map-equiv f x ＝ x' → map-equiv (map-conjugation-aut e f) y ＝ y'
  compute-value-conjugation-aut x refl refl refl =
    ap (map-equiv e ∘ map-equiv f) (is-retraction-map-inv-equiv e x)
```

### If `f : Aut X` and `f y ＝ y'`, and `e : X ≃ Y` satisfies `e x ＝ y` and `e x' ＝ y'`, then `(e⁻¹ ∘ f ∘ e) x ＝ x'`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2} (e : X ≃ Y) (f : Aut Y)
  where

  compute-value-conjugation-aut' :
    (x : X) {x' : X} {y y' : Y}
    (q : map-equiv e x ＝ y) (q' : map-equiv e x' ＝ y') →
    map-equiv f y ＝ y' → map-equiv (map-conjugation-aut' e f) x ＝ x'
  compute-value-conjugation-aut' x refl refl p =
    ap (map-inv-equiv e) p ∙ is-retraction-map-inv-equiv e _
```
