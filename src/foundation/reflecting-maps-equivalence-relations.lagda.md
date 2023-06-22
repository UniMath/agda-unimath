# Reflecting maps for equivalence relations

```agda
module foundation.reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
```

</details>

## Idea

A map `f : A → B` out of a type `A` equipped with an equivalence relation `R` is
said to **reflect** `R` if we have `R x y → f x ＝ f y` for every `x y : A`.

## Definitions

### Maps reflecting equivalence relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : Eq-Relation l2 A)
  where

  reflects-Eq-Relation : {l3 : Level} {B : UU l3} → (A → B) → UU (l1 ⊔ l2 ⊔ l3)
  reflects-Eq-Relation f = {x y : A} → sim-Eq-Relation R x y → (f x ＝ f y)

  reflecting-map-Eq-Relation : {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  reflecting-map-Eq-Relation B = Σ (A → B) reflects-Eq-Relation

  map-reflecting-map-Eq-Relation :
    {l3 : Level} {B : UU l3} → reflecting-map-Eq-Relation B → A → B
  map-reflecting-map-Eq-Relation = pr1

  reflects-map-reflecting-map-Eq-Relation :
    {l3 : Level} {B : UU l3} (f : reflecting-map-Eq-Relation B) →
    reflects-Eq-Relation (map-reflecting-map-Eq-Relation f)
  reflects-map-reflecting-map-Eq-Relation = pr2

  is-prop-reflects-Eq-Relation :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) →
    is-prop (reflects-Eq-Relation f)
  is-prop-reflects-Eq-Relation B f =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ y →
            is-prop-function-type (is-set-type-Set B (f x) (f y))))

  reflects-Eq-Relation-Prop :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) → Prop (l1 ⊔ l2 ⊔ l3)
  pr1 (reflects-Eq-Relation-Prop B f) = reflects-Eq-Relation f
  pr2 (reflects-Eq-Relation-Prop B f) = is-prop-reflects-Eq-Relation B f
```

## Properties

### Any surjective and effective map reflects the equivalence relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Relation l2 A) (B : Set l3)
  (q : A → type-Set B)
  where

  reflects-Eq-Relation-is-surjective-and-effective :
    is-surjective-and-effective R q → reflects-Eq-Relation R q
  reflects-Eq-Relation-is-surjective-and-effective E {x} {y} =
    map-inv-equiv (pr2 E x y)

  reflecting-map-Eq-Relation-is-surjective-and-effective :
    is-surjective-and-effective R q → reflecting-map-Eq-Relation R (type-Set B)
  pr1 (reflecting-map-Eq-Relation-is-surjective-and-effective E) = q
  pr2 (reflecting-map-Eq-Relation-is-surjective-and-effective E) =
    reflects-Eq-Relation-is-surjective-and-effective E
```

### Characterizing the identity type of reflecting maps into sets

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : Eq-Relation l2 A) (B : Set l3)
  (f : reflecting-map-Eq-Relation R (type-Set B))
  where

  htpy-reflecting-map-Eq-Relation :
    (g : reflecting-map-Eq-Relation R (type-Set B)) → UU (l1 ⊔ l3)
  htpy-reflecting-map-Eq-Relation g =
    pr1 f ~ pr1 g

  refl-htpy-reflecting-map-Eq-Relation :
    htpy-reflecting-map-Eq-Relation f
  refl-htpy-reflecting-map-Eq-Relation = refl-htpy

  htpy-eq-reflecting-map-Eq-Relation :
    (g : reflecting-map-Eq-Relation R (type-Set B)) →
    f ＝ g → htpy-reflecting-map-Eq-Relation g
  htpy-eq-reflecting-map-Eq-Relation .f refl =
    refl-htpy-reflecting-map-Eq-Relation

  is-contr-total-htpy-reflecting-map-Eq-Relation :
    is-contr
      ( Σ
        ( reflecting-map-Eq-Relation R (type-Set B))
        ( htpy-reflecting-map-Eq-Relation))
  is-contr-total-htpy-reflecting-map-Eq-Relation =
    is-contr-total-Eq-subtype
      ( is-contr-total-htpy (pr1 f))
      ( is-prop-reflects-Eq-Relation R B)
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-reflecting-map-Eq-Relation :
    (g : reflecting-map-Eq-Relation R (type-Set B)) →
    is-equiv (htpy-eq-reflecting-map-Eq-Relation g)
  is-equiv-htpy-eq-reflecting-map-Eq-Relation =
    fundamental-theorem-id
      is-contr-total-htpy-reflecting-map-Eq-Relation
      htpy-eq-reflecting-map-Eq-Relation

  extensionality-reflecting-map-Eq-Relation :
    (g : reflecting-map-Eq-Relation R (type-Set B)) →
    (f ＝ g) ≃ htpy-reflecting-map-Eq-Relation g
  pr1 (extensionality-reflecting-map-Eq-Relation g) =
    htpy-eq-reflecting-map-Eq-Relation g
  pr2 (extensionality-reflecting-map-Eq-Relation g) =
    is-equiv-htpy-eq-reflecting-map-Eq-Relation g

  eq-htpy-reflecting-map-Eq-Relation :
    (g : reflecting-map-Eq-Relation R (type-Set B)) →
    htpy-reflecting-map-Eq-Relation g → f ＝ g
  eq-htpy-reflecting-map-Eq-Relation g =
    map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-Eq-Relation g)
```
