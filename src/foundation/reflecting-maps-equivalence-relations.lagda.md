---
title: Reflecting maps for equivalence relations
---

```agda
{-# OPTIONS --without-K --exact-split #-}

module foundation.reflecting-maps-equivalence-relations where

open import foundation.equality-dependent-function-types
open import foundation.effective-maps-equivalence-relations
open import foundation.homotopies

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.functions
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtype-identity-principle
open import foundation-core.universe-levels
```

## Idea

A map `f : A → B` out of a type `A` equipped with an equivalence relation `R` is said to reflect `R` if we have `R x y → Id (f x) (f y)` for every `x y : A`.

## Definitions

### Maps reflecting equivalence relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where
  
  reflects-Eq-Rel : {l3 : Level} {B : UU l3} → (A → B) → UU (l1 ⊔ (l2 ⊔ l3))
  reflects-Eq-Rel f = {x y : A} → sim-Eq-Rel R x y → (f x ＝ f y)
  
  reflecting-map-Eq-Rel : {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  reflecting-map-Eq-Rel B = Σ (A → B) reflects-Eq-Rel

  map-reflecting-map-Eq-Rel :
    {l3 : Level} {B : UU l3} → reflecting-map-Eq-Rel B → A → B
  map-reflecting-map-Eq-Rel = pr1

  reflects-map-reflecting-map-Eq-Rel :
    {l3 : Level} {B : UU l3} (f : reflecting-map-Eq-Rel B) →
    reflects-Eq-Rel (map-reflecting-map-Eq-Rel f)
  reflects-map-reflecting-map-Eq-Rel = pr2

  is-prop-reflects-Eq-Rel :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) →
    is-prop (reflects-Eq-Rel f)
  is-prop-reflects-Eq-Rel B f =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ y →
            is-prop-function-type (is-set-type-Set B (f x) (f y))))

  reflects-Eq-Rel-Prop :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) → Prop (l1 ⊔ l2 ⊔ l3)
  pr1 (reflects-Eq-Rel-Prop B f) = reflects-Eq-Rel f
  pr2 (reflects-Eq-Rel-Prop B f) = is-prop-reflects-Eq-Rel B f
```

### Binary maps reflecting equivalence relations

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  binary-reflects-Eq-Rel :
    {l5 : Level} {C : UU l5} → (A → B → C) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflects-Eq-Rel f =
    {x x' : A} {y y' : B} →
    sim-Eq-Rel R x x' → sim-Eq-Rel S y y' → f x y ＝ f x' y'

  binary-reflecting-map-Eq-Rel :
    {l5 : Level} (C : UU l5) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflecting-map-Eq-Rel C = Σ (A → B → C) binary-reflects-Eq-Rel

  map-binary-reflecting-map-Eq-Rel :
    {l5 : Level} {C : UU l5} →
    binary-reflecting-map-Eq-Rel C → (A → B → C)
  map-binary-reflecting-map-Eq-Rel = pr1

  reflects-binary-reflecting-map-Eq-Rel :
    {l5 : Level} {C : UU l5} (f : binary-reflecting-map-Eq-Rel C) →
    binary-reflects-Eq-Rel (map-binary-reflecting-map-Eq-Rel f)
  reflects-binary-reflecting-map-Eq-Rel = pr2

  is-prop-binary-reflects-Eq-Rel :
    {l5 : Level} (C : Set l5) (f : A → B → type-Set C) →
    is-prop (binary-reflects-Eq-Rel f)
  is-prop-binary-reflects-Eq-Rel C f =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ x' →
            is-prop-Π'
              ( λ y →
                is-prop-Π'
                  ( λ y' →
                    is-prop-function-type
                      ( is-prop-function-type
                        ( is-set-type-Set C (f x y) (f x' y')))))))

  binary-reflects-Eq-Rel-Prop :
    {l5 : Level} (C : Set l5) →
    (A → B → type-Set C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (binary-reflects-Eq-Rel-Prop C f) = binary-reflects-Eq-Rel f
  pr2 (binary-reflects-Eq-Rel-Prop C f) = is-prop-binary-reflects-Eq-Rel C f
```

## Properties

### Any surjective and effective map reflects the equivalence relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : Set l3)
  (q : A → type-Set B)
  where

  reflects-Eq-Rel-is-surjective-and-effective :
    is-surjective-and-effective R q → reflects-Eq-Rel R q
  reflects-Eq-Rel-is-surjective-and-effective E {x} {y} =
    map-inv-equiv (pr2 E x y)

  reflecting-map-Eq-Rel-is-surjective-and-effective :
    is-surjective-and-effective R q → reflecting-map-Eq-Rel R (type-Set B)
  pr1 (reflecting-map-Eq-Rel-is-surjective-and-effective E) = q
  pr2 (reflecting-map-Eq-Rel-is-surjective-and-effective E) =
    reflects-Eq-Rel-is-surjective-and-effective E
```

### Characterizing the identity type of reflecting maps into sets

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Rel l2 A) (B : Set l3)
  (f : reflecting-map-Eq-Rel R (type-Set B))
  where

  htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) → UU _
  htpy-reflecting-map-Eq-Rel g =
    pr1 f ~ pr1 g
  
  refl-htpy-reflecting-map-Eq-Rel :
    htpy-reflecting-map-Eq-Rel f
  refl-htpy-reflecting-map-Eq-Rel = refl-htpy
  
  htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    f ＝ g → htpy-reflecting-map-Eq-Rel g
  htpy-eq-reflecting-map-Eq-Rel .f refl =
    refl-htpy-reflecting-map-Eq-Rel

  is-contr-total-htpy-reflecting-map-Eq-Rel :
    is-contr
      ( Σ (reflecting-map-Eq-Rel R (type-Set B)) htpy-reflecting-map-Eq-Rel)
  is-contr-total-htpy-reflecting-map-Eq-Rel =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (pr1 f))
      ( is-prop-reflects-Eq-Rel R B)
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    is-equiv (htpy-eq-reflecting-map-Eq-Rel g)
  is-equiv-htpy-eq-reflecting-map-Eq-Rel =
    fundamental-theorem-id
      is-contr-total-htpy-reflecting-map-Eq-Rel
      htpy-eq-reflecting-map-Eq-Rel

  extensionality-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    (f ＝ g) ≃ htpy-reflecting-map-Eq-Rel g
  pr1 (extensionality-reflecting-map-Eq-Rel g) = htpy-eq-reflecting-map-Eq-Rel g
  pr2 (extensionality-reflecting-map-Eq-Rel g) =
    is-equiv-htpy-eq-reflecting-map-Eq-Rel g

  eq-htpy-reflecting-map-Eq-Rel :
    (g : reflecting-map-Eq-Rel R (type-Set B)) →
    htpy-reflecting-map-Eq-Rel g → f ＝ g
  eq-htpy-reflecting-map-Eq-Rel g =
    map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-Eq-Rel g)
```

### Characterizing the identity type of binary reflecting maps into sets

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  (C : Set l5) (f : binary-reflecting-map-Eq-Rel R S (type-Set C))
  where

  htpy-binary-reflecting-map-Eq-Rel :
    (g : binary-reflecting-map-Eq-Rel R S (type-Set C)) → UU (l1 ⊔ l3 ⊔ l5)
  htpy-binary-reflecting-map-Eq-Rel g =
    (x : A) (y : B) →
    map-binary-reflecting-map-Eq-Rel R S f x y ＝
    map-binary-reflecting-map-Eq-Rel R S g x y

  refl-htpy-binary-reflecting-map-Eq-Rel :
    htpy-binary-reflecting-map-Eq-Rel f
  refl-htpy-binary-reflecting-map-Eq-Rel x y = refl

  htpy-eq-binary-reflecting-map-Eq-Rel :
    (g : binary-reflecting-map-Eq-Rel R S (type-Set C)) →
    (f ＝ g) → htpy-binary-reflecting-map-Eq-Rel g
  htpy-eq-binary-reflecting-map-Eq-Rel .f refl =
    refl-htpy-binary-reflecting-map-Eq-Rel

  is-contr-total-htpy-binary-reflecting-map-Eq-Rel :
    is-contr
      ( Σ ( binary-reflecting-map-Eq-Rel R S (type-Set C))
          ( htpy-binary-reflecting-map-Eq-Rel))
  is-contr-total-htpy-binary-reflecting-map-Eq-Rel =
    is-contr-total-Eq-subtype
      ( is-contr-total-Eq-Π
        ( λ x → (λ g → map-binary-reflecting-map-Eq-Rel R S f x ~ g))
        ( λ x → is-contr-total-htpy (map-binary-reflecting-map-Eq-Rel R S f x)))
      ( is-prop-binary-reflects-Eq-Rel R S C)
      ( map-binary-reflecting-map-Eq-Rel R S f)
      ( λ x → refl-htpy)
      ( reflects-binary-reflecting-map-Eq-Rel R S f)

  is-equiv-htpy-eq-binary-reflecting-map-Eq-Rel :
    (g : binary-reflecting-map-Eq-Rel R S (type-Set C)) →
    is-equiv (htpy-eq-binary-reflecting-map-Eq-Rel g)
  is-equiv-htpy-eq-binary-reflecting-map-Eq-Rel =
    fundamental-theorem-id
      is-contr-total-htpy-binary-reflecting-map-Eq-Rel
      htpy-eq-binary-reflecting-map-Eq-Rel

  extensionality-binary-reflecting-map-Eq-Rel :
    (g : binary-reflecting-map-Eq-Rel R S (type-Set C)) →
    (f ＝ g) ≃ htpy-binary-reflecting-map-Eq-Rel g
  pr1 (extensionality-binary-reflecting-map-Eq-Rel g) =
    htpy-eq-binary-reflecting-map-Eq-Rel g
  pr2 (extensionality-binary-reflecting-map-Eq-Rel g) =
    is-equiv-htpy-eq-binary-reflecting-map-Eq-Rel g

  eq-htpy-binary-reflecting-map-Eq-Rel :
    (g : binary-reflecting-map-Eq-Rel R S (type-Set C)) →
    htpy-binary-reflecting-map-Eq-Rel g → (f ＝ g)
  eq-htpy-binary-reflecting-map-Eq-Rel g =
    map-inv-equiv (extensionality-binary-reflecting-map-Eq-Rel g)
```

### Composition of reflecting maps

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B) {C : UU l5}
  where

  comp-reflecting-map-Eq-Rel :
    reflecting-map-Eq-Rel S C → (f : A → B) →
    ({x y : A} → sim-Eq-Rel R x y → sim-Eq-Rel S (f x) (f y)) →
    reflecting-map-Eq-Rel R C
  pr1 (comp-reflecting-map-Eq-Rel g f H) = map-reflecting-map-Eq-Rel S g ∘ f
  pr2 (comp-reflecting-map-Eq-Rel g f H) {x} {y} r =
    reflects-map-reflecting-map-Eq-Rel S g (H r)
```
