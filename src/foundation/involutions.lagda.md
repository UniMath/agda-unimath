# Involutions

```agda
module foundation.involutions where

open import foundation-core.involutions public
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
```

</details>

## Idea

An **involution** on a type `A` is a map `f : A → A` such that `(f ∘ f) ~ id`.

## Properties

### Involutions are their own inverse

```agda
htpy-own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} →
  is-involution-aut f → map-inv-equiv f ~ map-equiv f
htpy-own-inverse-is-involution {f = f} is-involution-f x =
  is-injective-map-equiv f
    ( htpy-eq-equiv (right-inverse-law-equiv f) x ∙
      inv (is-involution-f x))

own-inverse-is-involution :
  {l : Level} {A : UU l} {f : Aut A} →
  is-involution-aut f → inv-equiv f ＝ f
own-inverse-is-involution {f = f} =
  eq-htpy-equiv ∘ htpy-own-inverse-is-involution {f = f}
```

### Characterizing equality of involutions

```agda
module _
  {l : Level} {A : UU l}
  where

  coherence-htpy-involution :
    (s t : involution A) → map-involution s ~ map-involution t → UU l
  coherence-htpy-involution s t H =
    ( is-involution-map-involution s) ~
    ( htpy-comp-horizontal H H ∙h is-involution-map-involution t)

  htpy-involution : (s t : involution A) → UU l
  htpy-involution s t =
    Σ ( map-involution s ~ map-involution t)
      ( coherence-htpy-involution s t)

  refl-htpy-involution : (s : involution A) → htpy-involution s s
  pr1 (refl-htpy-involution s) = refl-htpy
  pr2 (refl-htpy-involution s) = refl-htpy

  htpy-eq-involution : (s t : involution A) → s ＝ t → htpy-involution s t
  htpy-eq-involution s .s refl = refl-htpy-involution s

  is-contr-total-htpy-involution :
    (s : involution A) → is-contr (Σ (involution A) (htpy-involution s))
  is-contr-total-htpy-involution s =
    is-contr-total-Eq-structure
      ( λ x z → coherence-htpy-involution s (x , z))
      ( is-contr-total-htpy (map-involution s))
      ( map-involution s , refl-htpy)
      ( is-contr-total-htpy (is-involution-map-involution s))

  is-equiv-htpy-eq-involution :
    (s t : involution A) → is-equiv (htpy-eq-involution s t)
  is-equiv-htpy-eq-involution s =
    fundamental-theorem-id
      ( is-contr-total-htpy-involution s)
      ( htpy-eq-involution s)

  extensionality-involution :
    (s t : involution A) → (s ＝ t) ≃ (htpy-involution s t)
  pr1 (extensionality-involution s t) = htpy-eq-involution s t
  pr2 (extensionality-involution s t) = is-equiv-htpy-eq-involution s t

  eq-htpy-involution : (s t : involution A) → htpy-involution s t → s ＝ t
  eq-htpy-involution s t = map-inv-equiv (extensionality-involution s t)
```
