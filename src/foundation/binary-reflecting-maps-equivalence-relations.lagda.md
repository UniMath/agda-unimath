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

Consider two types `A` and `B` equipped with equivalence relations `R` and `S`.
A binary reflecting map from `A` to `B` to `X` is a binary map `f : A → B → X`
such that for any to `R`-related elements `x` and `x'` in `A` and any two
`S`-related elements `y` and `y'` in `B` we have `f x y ＝ f x' y'` in `X`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (R : equivalence-relation l3 A) (S : equivalence-relation l4 B)
  where

  binary-reflects-equivalence-relation :
    {X : UU l5} (f : A → B → X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflects-equivalence-relation f =
    {x x' : A} {y y' : B} →
    sim-equivalence-relation R x x' → sim-equivalence-relation S y y' →
    f x y ＝ f x' y'

  binary-reflecting-map-equivalence-relation :
    (X : UU l5) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflecting-map-equivalence-relation X =
    Σ (A → B → X) binary-reflects-equivalence-relation

  map-binary-reflecting-map-equivalence-relation :
    {X : UU l5} → binary-reflecting-map-equivalence-relation X → A → B → X
  map-binary-reflecting-map-equivalence-relation = pr1

  reflects-binary-reflecting-map-equivalence-relation :
    {X : UU l5} (f : binary-reflecting-map-equivalence-relation X) →
    binary-reflects-equivalence-relation
      ( map-binary-reflecting-map-equivalence-relation f)
  reflects-binary-reflecting-map-equivalence-relation = pr2

  is-prop-binary-reflects-equivalence-relation :
    (X : Set l5) (f : A → B → type-Set X) →
    is-prop (binary-reflects-equivalence-relation f)
  is-prop-binary-reflects-equivalence-relation X f =
    is-prop-implicit-Π
      ( λ x →
        is-prop-implicit-Π
          ( λ x' →
            is-prop-implicit-Π
              ( λ y →
                is-prop-implicit-Π
                  ( λ y' →
                    is-prop-function-type
                      ( is-prop-function-type
                        ( is-set-type-Set X (f x y) (f x' y')))))))

  binary-reflects-prop-equivalence-relation :
    (X : Set l5) (f : A → B → type-Set X) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (binary-reflects-prop-equivalence-relation X f) =
    binary-reflects-equivalence-relation f
  pr2 (binary-reflects-prop-equivalence-relation X f) =
    is-prop-binary-reflects-equivalence-relation X f
```

### Characterizing the identity type of binary reflecting maps into sets

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} (R : equivalence-relation l2 A)
  {B : UU l3} (S : equivalence-relation l4 B)
  (C : Set l5) (f : binary-reflecting-map-equivalence-relation R S (type-Set C))
  where

  htpy-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    UU (l1 ⊔ l3 ⊔ l5)
  htpy-binary-reflecting-map-equivalence-relation g =
    (x : A) (y : B) →
    map-binary-reflecting-map-equivalence-relation R S f x y ＝
    map-binary-reflecting-map-equivalence-relation R S g x y

  refl-htpy-binary-reflecting-map-equivalence-relation :
    htpy-binary-reflecting-map-equivalence-relation f
  refl-htpy-binary-reflecting-map-equivalence-relation x y = refl

  htpy-eq-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    (f ＝ g) → htpy-binary-reflecting-map-equivalence-relation g
  htpy-eq-binary-reflecting-map-equivalence-relation .f refl =
    refl-htpy-binary-reflecting-map-equivalence-relation

  is-torsorial-htpy-binary-reflecting-map-equivalence-relation :
    is-torsorial (htpy-binary-reflecting-map-equivalence-relation)
  is-torsorial-htpy-binary-reflecting-map-equivalence-relation =
    is-torsorial-Eq-subtype
      ( is-torsorial-Eq-Π
        ( λ x →
          is-torsorial-htpy
            ( map-binary-reflecting-map-equivalence-relation R S f x)))
      ( is-prop-binary-reflects-equivalence-relation R S C)
      ( map-binary-reflecting-map-equivalence-relation R S f)
      ( λ x → refl-htpy)
      ( reflects-binary-reflecting-map-equivalence-relation R S f)

  is-equiv-htpy-eq-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    is-equiv (htpy-eq-binary-reflecting-map-equivalence-relation g)
  is-equiv-htpy-eq-binary-reflecting-map-equivalence-relation =
    fundamental-theorem-id
      is-torsorial-htpy-binary-reflecting-map-equivalence-relation
      htpy-eq-binary-reflecting-map-equivalence-relation

  extensionality-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    (f ＝ g) ≃ htpy-binary-reflecting-map-equivalence-relation g
  pr1 (extensionality-binary-reflecting-map-equivalence-relation g) =
    htpy-eq-binary-reflecting-map-equivalence-relation g
  pr2 (extensionality-binary-reflecting-map-equivalence-relation g) =
    is-equiv-htpy-eq-binary-reflecting-map-equivalence-relation g

  eq-htpy-binary-reflecting-map-equivalence-relation :
    (g : binary-reflecting-map-equivalence-relation R S (type-Set C)) →
    htpy-binary-reflecting-map-equivalence-relation g → (f ＝ g)
  eq-htpy-binary-reflecting-map-equivalence-relation g =
    map-inv-equiv (extensionality-binary-reflecting-map-equivalence-relation g)
```
