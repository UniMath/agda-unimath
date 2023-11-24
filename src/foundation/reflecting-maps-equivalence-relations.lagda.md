# Reflecting maps for equivalence relations

```agda
module foundation.reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.effective-maps-equivalence-relations
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.subtype-identity-principle
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A map `f : A → B` out of a type `A` equipped with an equivalence relation `R` is
said to **reflect** `R` if we have `R x y → f x ＝ f y` for every `x y : A`.

## Definitions

### Maps reflecting equivalence relations

```agda
module _
  {l1 l2 : Level} {A : UU l1} (R : equivalence-relation l2 A)
  where

  reflects-equivalence-relation :
    {l3 : Level} {B : UU l3} → (A → B) → UU (l1 ⊔ l2 ⊔ l3)
  reflects-equivalence-relation f =
    {x y : A} → sim-equivalence-relation R x y → (f x ＝ f y)

  reflecting-map-equivalence-relation : {l3 : Level} → UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  reflecting-map-equivalence-relation B =
    Σ (A → B) reflects-equivalence-relation

  map-reflecting-map-equivalence-relation :
    {l3 : Level} {B : UU l3} → reflecting-map-equivalence-relation B → A → B
  map-reflecting-map-equivalence-relation = pr1

  reflects-map-reflecting-map-equivalence-relation :
    {l3 : Level} {B : UU l3} (f : reflecting-map-equivalence-relation B) →
    reflects-equivalence-relation (map-reflecting-map-equivalence-relation f)
  reflects-map-reflecting-map-equivalence-relation = pr2

  is-prop-reflects-equivalence-relation :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) →
    is-prop (reflects-equivalence-relation f)
  is-prop-reflects-equivalence-relation B f =
    is-prop-Π'
      ( λ x →
        is-prop-Π'
          ( λ y →
            is-prop-function-type (is-set-type-Set B (f x) (f y))))

  reflects-prop-equivalence-relation :
    {l3 : Level} (B : Set l3) (f : A → type-Set B) → Prop (l1 ⊔ l2 ⊔ l3)
  pr1 (reflects-prop-equivalence-relation B f) = reflects-equivalence-relation f
  pr2 (reflects-prop-equivalence-relation B f) =
    is-prop-reflects-equivalence-relation B f
```

## Properties

### Any surjective and effective map reflects the equivalence relation

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (q : A → type-Set B)
  where

  reflects-equivalence-relation-is-surjective-and-effective :
    is-surjective-and-effective R q → reflects-equivalence-relation R q
  reflects-equivalence-relation-is-surjective-and-effective E {x} {y} =
    map-inv-equiv (pr2 E x y)

  reflecting-map-equivalence-relation-is-surjective-and-effective :
    is-surjective-and-effective R q →
    reflecting-map-equivalence-relation R (type-Set B)
  pr1 (reflecting-map-equivalence-relation-is-surjective-and-effective E) = q
  pr2 (reflecting-map-equivalence-relation-is-surjective-and-effective E) =
    reflects-equivalence-relation-is-surjective-and-effective E
```

### Characterizing the identity type of reflecting maps into sets

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} (R : equivalence-relation l2 A) (B : Set l3)
  (f : reflecting-map-equivalence-relation R (type-Set B))
  where

  htpy-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) → UU (l1 ⊔ l3)
  htpy-reflecting-map-equivalence-relation g =
    pr1 f ~ pr1 g

  refl-htpy-reflecting-map-equivalence-relation :
    htpy-reflecting-map-equivalence-relation f
  refl-htpy-reflecting-map-equivalence-relation = refl-htpy

  htpy-eq-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    f ＝ g → htpy-reflecting-map-equivalence-relation g
  htpy-eq-reflecting-map-equivalence-relation .f refl =
    refl-htpy-reflecting-map-equivalence-relation

  is-torsorial-htpy-reflecting-map-equivalence-relation :
    is-torsorial (htpy-reflecting-map-equivalence-relation)
  is-torsorial-htpy-reflecting-map-equivalence-relation =
    is-torsorial-Eq-subtype
      ( is-torsorial-htpy (pr1 f))
      ( is-prop-reflects-equivalence-relation R B)
      ( pr1 f)
      ( refl-htpy)
      ( pr2 f)

  is-equiv-htpy-eq-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    is-equiv (htpy-eq-reflecting-map-equivalence-relation g)
  is-equiv-htpy-eq-reflecting-map-equivalence-relation =
    fundamental-theorem-id
      is-torsorial-htpy-reflecting-map-equivalence-relation
      htpy-eq-reflecting-map-equivalence-relation

  extensionality-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    (f ＝ g) ≃ htpy-reflecting-map-equivalence-relation g
  pr1 (extensionality-reflecting-map-equivalence-relation g) =
    htpy-eq-reflecting-map-equivalence-relation g
  pr2 (extensionality-reflecting-map-equivalence-relation g) =
    is-equiv-htpy-eq-reflecting-map-equivalence-relation g

  eq-htpy-reflecting-map-equivalence-relation :
    (g : reflecting-map-equivalence-relation R (type-Set B)) →
    htpy-reflecting-map-equivalence-relation g → f ＝ g
  eq-htpy-reflecting-map-equivalence-relation g =
    map-inv-is-equiv (is-equiv-htpy-eq-reflecting-map-equivalence-relation g)
```
