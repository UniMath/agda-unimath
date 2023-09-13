# Binary reflecting maps of equivalence relations

```agda
module foundation.binary-reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
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
```

</details>

## Idea

Consider two types `A` and `B` equipped with equivalence relations `R` and `S`.
A binary reflecting map from `A` to `B` to `X` is a binary map `f : A → B → X`
such that for any to `R`-related elements `x` and `x'` in `A` and any two
`S`-related elements `y` and `y'` in `B` we have `f x y ＝ f x' y'` in `X`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (R : Equivalence-Relation l3 A) (S : Equivalence-Relation l4 B)
  where

  binary-reflects-Equivalence-Relation :
    {X : UU l5} (f : A → B → X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflects-Equivalence-Relation f =
    {x x' : A} {y y' : B} →
    sim-Equivalence-Relation R x x' → sim-Equivalence-Relation S y y' →
    f x y ＝ f x' y'

  binary-reflecting-map-Equivalence-Relation :
    (X : UU l5) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflecting-map-Equivalence-Relation X =
    Σ (A → B → X) binary-reflects-Equivalence-Relation

  map-binary-reflecting-map-Equivalence-Relation :
    {X : UU l5} → binary-reflecting-map-Equivalence-Relation X → A → B → X
  map-binary-reflecting-map-Equivalence-Relation = pr1

  reflects-binary-reflecting-map-Equivalence-Relation :
    {X : UU l5} (f : binary-reflecting-map-Equivalence-Relation X) →
    binary-reflects-Equivalence-Relation
      ( map-binary-reflecting-map-Equivalence-Relation f)
  reflects-binary-reflecting-map-Equivalence-Relation = pr2

  is-prop-binary-reflects-Equivalence-Relation :
    (X : Set l5) (f : A → B → type-Set X) →
    is-prop (binary-reflects-Equivalence-Relation f)
  is-prop-binary-reflects-Equivalence-Relation X f =
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
                        ( is-set-type-Set X (f x y) (f x' y')))))))

  binary-reflects-Equivalence-Relation-Prop :
    (X : Set l5) (f : A → B → type-Set X) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (binary-reflects-Equivalence-Relation-Prop X f) =
    binary-reflects-Equivalence-Relation f
  pr2 (binary-reflects-Equivalence-Relation-Prop X f) =
    is-prop-binary-reflects-Equivalence-Relation X f
```

### Characterizing the identity type of binary reflecting maps into sets

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  (C : Set l5) (f : binary-reflecting-map-Equivalence-Relation R S (type-Set C))
  where

  htpy-binary-reflecting-map-Equivalence-Relation :
    (g : binary-reflecting-map-Equivalence-Relation R S (type-Set C)) →
    UU (l1 ⊔ l3 ⊔ l5)
  htpy-binary-reflecting-map-Equivalence-Relation g =
    (x : A) (y : B) →
    map-binary-reflecting-map-Equivalence-Relation R S f x y ＝
    map-binary-reflecting-map-Equivalence-Relation R S g x y

  refl-htpy-binary-reflecting-map-Equivalence-Relation :
    htpy-binary-reflecting-map-Equivalence-Relation f
  refl-htpy-binary-reflecting-map-Equivalence-Relation x y = refl

  htpy-eq-binary-reflecting-map-Equivalence-Relation :
    (g : binary-reflecting-map-Equivalence-Relation R S (type-Set C)) →
    (f ＝ g) → htpy-binary-reflecting-map-Equivalence-Relation g
  htpy-eq-binary-reflecting-map-Equivalence-Relation .f refl =
    refl-htpy-binary-reflecting-map-Equivalence-Relation

  is-contr-total-htpy-binary-reflecting-map-Equivalence-Relation :
    is-contr
      ( Σ ( binary-reflecting-map-Equivalence-Relation R S (type-Set C))
          ( htpy-binary-reflecting-map-Equivalence-Relation))
  is-contr-total-htpy-binary-reflecting-map-Equivalence-Relation =
    is-contr-total-Eq-subtype
      ( is-contr-total-Eq-Π
        ( λ x g → map-binary-reflecting-map-Equivalence-Relation R S f x ~ g)
        ( λ x →
          is-contr-total-htpy
            ( map-binary-reflecting-map-Equivalence-Relation R S f x)))
      ( is-prop-binary-reflects-Equivalence-Relation R S C)
      ( map-binary-reflecting-map-Equivalence-Relation R S f)
      ( λ x → refl-htpy)
      ( reflects-binary-reflecting-map-Equivalence-Relation R S f)

  is-equiv-htpy-eq-binary-reflecting-map-Equivalence-Relation :
    (g : binary-reflecting-map-Equivalence-Relation R S (type-Set C)) →
    is-equiv (htpy-eq-binary-reflecting-map-Equivalence-Relation g)
  is-equiv-htpy-eq-binary-reflecting-map-Equivalence-Relation =
    fundamental-theorem-id
      is-contr-total-htpy-binary-reflecting-map-Equivalence-Relation
      htpy-eq-binary-reflecting-map-Equivalence-Relation

  extensionality-binary-reflecting-map-Equivalence-Relation :
    (g : binary-reflecting-map-Equivalence-Relation R S (type-Set C)) →
    (f ＝ g) ≃ htpy-binary-reflecting-map-Equivalence-Relation g
  pr1 (extensionality-binary-reflecting-map-Equivalence-Relation g) =
    htpy-eq-binary-reflecting-map-Equivalence-Relation g
  pr2 (extensionality-binary-reflecting-map-Equivalence-Relation g) =
    is-equiv-htpy-eq-binary-reflecting-map-Equivalence-Relation g

  eq-htpy-binary-reflecting-map-Equivalence-Relation :
    (g : binary-reflecting-map-Equivalence-Relation R S (type-Set C)) →
    htpy-binary-reflecting-map-Equivalence-Relation g → (f ＝ g)
  eq-htpy-binary-reflecting-map-Equivalence-Relation g =
    map-inv-equiv (extensionality-binary-reflecting-map-Equivalence-Relation g)
```
