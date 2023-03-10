# Reflecting maps for equivalence relations

```agda
module foundation.reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.effective-maps-equivalence-relations
open import foundation.equality-dependent-function-types
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

</details>

## Idea

A map `f : A → B` out of a type `A` equipped with an equivalence relation `R` is said to reflect `R` if we have `R x y → Id (f x) (f y)` for every `x y : A`.

## Definitions

### Maps reflecting equivalence relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Rel l2 A)
  where

  reflects-Eq-Rel : {l3 : Level} {B : UU l3} → (A → B) → UU (l1 ⊔ l2 ⊔ l3)
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
