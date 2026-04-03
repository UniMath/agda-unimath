# Equality of lists

```agda
module lists.equality-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Idea

We define
{{#concept "observational equality" Disambiguation="of lists" Agda=Eq-list}} of
[lists](lists.lists.md), and show that it characterizes the
[identity type](foundation.identity-types.md) of lists.

## Definition

```agda
module _
  {l1 : Level}
  {A : UU l1}
  where

  Eq-list : Relation l1 (list A)
  Eq-list nil nil = raise-unit l1
  Eq-list nil (cons x l') = raise-empty l1
  Eq-list (cons x l) nil = raise-empty l1
  Eq-list (cons x l) (cons x' l') = (x ＝ x') × Eq-list l l'
```

## Properties

### Reflexivity of observational equality

```agda
module _
  {l1 : Level}
  {A : UU l1}
  where

  refl-Eq-list : (l : list A) → Eq-list l l
  refl-Eq-list nil = raise-star
  refl-Eq-list (cons x l) = pair refl (refl-Eq-list l)
```

### Logical equivalence of observational equality and identity

```agda
module _
  {l1 : Level}
  {A : UU l1}
  where

  Eq-eq-list :
    (l l' : list A) → l ＝ l' → Eq-list l l'
  Eq-eq-list l .l refl = refl-Eq-list l

  eq-Eq-list :
    (l l' : list A) → Eq-list l l' → l ＝ l'
  eq-Eq-list nil nil (map-raise star) = refl
  eq-Eq-list nil (cons x l') (map-raise f) = ex-falso f
  eq-Eq-list (cons x l) nil (map-raise f) = ex-falso f
  eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
    ap (cons x) (eq-Eq-list l l' e)
```

### The logical equivalence is an equivalence

```agda
module _
  {l1 : Level}
  {A : UU l1}
  where

  abstract
    square-eq-Eq-list :
      {x : A} {l l' : list A} (p : l ＝ l') →
      Eq-eq-list (cons x l) (cons x l') (ap (cons x) p) ＝
      pair refl (Eq-eq-list l l' p)
    square-eq-Eq-list refl = refl

    is-section-eq-Eq-list :
      (l l' : list A) (e : Eq-list l l') →
      Eq-eq-list l l' (eq-Eq-list l l' e) ＝ e
    is-section-eq-Eq-list nil nil e = eq-is-contr is-contr-raise-unit
    is-section-eq-Eq-list nil (cons x l') e = ex-falso (is-empty-raise-empty e)
    is-section-eq-Eq-list (cons x l) nil e = ex-falso (is-empty-raise-empty e)
    is-section-eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
      ( square-eq-Eq-list (eq-Eq-list l l' e)) ∙
      ( eq-pair-eq-fiber (is-section-eq-Eq-list l l' e))

    eq-Eq-refl-Eq-list :
      (l : list A) →
      eq-Eq-list l l (refl-Eq-list l) ＝ refl
    eq-Eq-refl-Eq-list nil = refl
    eq-Eq-refl-Eq-list (cons x l) = ap² (cons x) (eq-Eq-refl-Eq-list l)

    is-retraction-eq-Eq-list :
      (l l' : list A) (p : l ＝ l') →
      eq-Eq-list l l' (Eq-eq-list l l' p) ＝ p
    is-retraction-eq-Eq-list nil .nil refl = refl
    is-retraction-eq-Eq-list (cons x l) .(cons x l) refl =
      eq-Eq-refl-Eq-list (cons x l)

  is-equiv-Eq-eq-list :
    (l l' : list A) → is-equiv (Eq-eq-list l l')
  is-equiv-Eq-eq-list l l' =
    is-equiv-is-invertible
      ( eq-Eq-list l l')
      ( is-section-eq-Eq-list l l')
      ( is-retraction-eq-Eq-list l l')

  equiv-Eq-list :
    (l l' : list A) → (l ＝ l') ≃ Eq-list l l'
  equiv-Eq-list l l' =
    pair (Eq-eq-list l l') (is-equiv-Eq-eq-list l l')

  is-torsorial-Eq-list :
    (l : list A) →
    is-torsorial (Eq-list l)
  is-torsorial-Eq-list l =
    is-contr-equiv'
      ( Σ (list A) (Id l))
      ( equiv-tot (equiv-Eq-list l))
      ( is-torsorial-Id l)
```

### Truncation of list types

```agda
module _
  {l : Level}
  {A : UU l}
  where

  abstract
    is-trunc-Eq-list :
      (k : 𝕋) → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
      (l l' : list A) → is-trunc (succ-𝕋 k) (Eq-list l l')
    is-trunc-Eq-list k H nil nil =
      is-trunc-is-contr (succ-𝕋 k) is-contr-raise-unit
    is-trunc-Eq-list k H nil (cons x l') =
      is-trunc-is-empty k is-empty-raise-empty
    is-trunc-Eq-list k H (cons x l) nil =
      is-trunc-is-empty k is-empty-raise-empty
    is-trunc-Eq-list k H (cons x l) (cons y l') =
      is-trunc-product (succ-𝕋 k) (H x y) (is-trunc-Eq-list k H l l')

  is-trunc-list :
    (k : 𝕋) → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
    is-trunc (succ-𝕋 (succ-𝕋 k)) (list A)
  is-trunc-list k H l l' =
    is-trunc-equiv
      ( succ-𝕋 k)
      ( Eq-list l l')
      ( equiv-Eq-list l l')
      ( is-trunc-Eq-list k H l l')

  is-set-list :
    is-set A → is-set (list A)
  is-set-list = is-trunc-list neg-two-𝕋

list-Set : {l : Level} → Set l → Set l
list-Set (A , is-set-A) = (list A , is-set-list is-set-A)
```
