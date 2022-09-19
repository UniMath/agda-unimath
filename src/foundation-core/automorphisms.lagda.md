---
title: Automorphisms
---

```agda
module foundation-core.automorphisms where

open import foundation.cartesian-product-types using (_×_)
open import foundation.contractible-types using
  ( is-contr; is-contr-total-path; is-contr-equiv')
open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.equivalences using
  ( _≃_; map-equiv; map-inv-equiv; issec-map-inv-equiv; isretr-map-inv-equiv;
    is-equiv; map-inv-is-equiv; id-equiv)
open import foundation.functions using (_∘_; id)
open import foundation.functoriality-dependent-pair-types using
  ( equiv-tot)
open import foundation.fundamental-theorem-of-identity-types using
  ( fundamental-theorem-id)
open import foundation.homotopies using
  ( _~_; refl-htpy; is-contr-total-htpy; equiv-concat-htpy; right-unit-htpy)
open import foundation.identity-types using (_＝_; _∙_; ap; refl; right-unit)
open import foundation.sets using
  ( is-set; is-set-equiv-is-set; Set; type-Set; is-set-type-Set;
    equiv-Set)
open import foundation.structure-identity-principle using
  ( is-contr-total-Eq-structure)
open import foundation.universe-levels using (Level; UU; lsuc; _⊔_)

open import structured-types.pointed-types using (Pointed-Type)
```

## Idea

An automorphism on a type `A` is an equivalence `A ≃ A`. We will just reuse the infrastructure of equivalences for automorphisms.

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
