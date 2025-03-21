# Equality of lists

```agda
module lists.equality-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.dependent-products-truncated-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.negation
open import foundation.raising-universe-levels
open import foundation.raising-universe-levels-unit-type
open import foundation.sets
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.maybe

open import lists.lists
```

</details>

## Properties

### Characterizing the identity type of lists

```agda
Eq-list : {l1 : Level} {A : UU l1} → list A → list A → UU l1
Eq-list {l1} nil nil = raise-unit l1
Eq-list {l1} nil (cons x l') = raise-empty l1
Eq-list {l1} (cons x l) nil = raise-empty l1
Eq-list {l1} (cons x l) (cons x' l') = (Id x x') × Eq-list l l'

refl-Eq-list : {l1 : Level} {A : UU l1} (l : list A) → Eq-list l l
refl-Eq-list nil = raise-star
refl-Eq-list (cons x l) = pair refl (refl-Eq-list l)

Eq-eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' → Eq-list l l'
Eq-eq-list l .l refl = refl-Eq-list l

eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Eq-list l l' → Id l l'
eq-Eq-list nil nil (map-raise star) = refl
eq-Eq-list nil (cons x l') (map-raise f) = ex-falso f
eq-Eq-list (cons x l) nil (map-raise f) = ex-falso f
eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
  ap (cons x) (eq-Eq-list l l' e)

square-eq-Eq-list :
  {l1 : Level} {A : UU l1} {x : A} {l l' : list A} (p : Id l l') →
  Id
    ( Eq-eq-list (cons x l) (cons x l') (ap (cons x) p))
    ( pair refl (Eq-eq-list l l' p))
square-eq-Eq-list refl = refl

is-section-eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) (e : Eq-list l l') →
  Id (Eq-eq-list l l' (eq-Eq-list l l' e)) e
is-section-eq-Eq-list nil nil e = eq-is-contr is-contr-raise-unit
is-section-eq-Eq-list nil (cons x l') e = ex-falso (is-empty-raise-empty e)
is-section-eq-Eq-list (cons x l) nil e = ex-falso (is-empty-raise-empty e)
is-section-eq-Eq-list (cons x l) (cons .x l') (pair refl e) =
  ( square-eq-Eq-list (eq-Eq-list l l' e)) ∙
  ( eq-pair-eq-fiber (is-section-eq-Eq-list l l' e))

eq-Eq-refl-Eq-list :
  {l1 : Level} {A : UU l1} (l : list A) →
  Id (eq-Eq-list l l (refl-Eq-list l)) refl
eq-Eq-refl-Eq-list nil = refl
eq-Eq-refl-Eq-list (cons x l) = ap² (cons x) (eq-Eq-refl-Eq-list l)

is-retraction-eq-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) (p : Id l l') →
  Id (eq-Eq-list l l' (Eq-eq-list l l' p)) p
is-retraction-eq-Eq-list nil .nil refl = refl
is-retraction-eq-Eq-list (cons x l) .(cons x l) refl =
  eq-Eq-refl-Eq-list (cons x l)

is-equiv-Eq-eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → is-equiv (Eq-eq-list l l')
is-equiv-Eq-eq-list l l' =
  is-equiv-is-invertible
    ( eq-Eq-list l l')
    ( is-section-eq-Eq-list l l')
    ( is-retraction-eq-Eq-list l l')

equiv-Eq-list :
  {l1 : Level} {A : UU l1} (l l' : list A) → Id l l' ≃ Eq-list l l'
equiv-Eq-list l l' =
  pair (Eq-eq-list l l') (is-equiv-Eq-eq-list l l')

is-torsorial-Eq-list :
  {l1 : Level} {A : UU l1} (l : list A) →
  is-torsorial (Eq-list l)
is-torsorial-Eq-list {A = A} l =
  is-contr-equiv'
    ( Σ (list A) (Id l))
    ( equiv-tot (equiv-Eq-list l))
    ( is-torsorial-Id l)

is-trunc-Eq-list :
  (k : 𝕋) {l : Level} {A : UU l} → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
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
  (k : 𝕋) {l : Level} {A : UU l} → is-trunc (succ-𝕋 (succ-𝕋 k)) A →
  is-trunc (succ-𝕋 (succ-𝕋 k)) (list A)
is-trunc-list k H l l' =
  is-trunc-equiv
    ( succ-𝕋 k)
    ( Eq-list l l')
    ( equiv-Eq-list l l')
    ( is-trunc-Eq-list k H l l')

is-set-list :
  {l : Level} {A : UU l} → is-set A → is-set (list A)
is-set-list = is-trunc-list neg-two-𝕋

list-Set : {l : Level} → Set l → Set l
list-Set A = pair (list (type-Set A)) (is-set-list (is-set-type-Set A))
```
