# Binary reflecting maps of equivalence relations

```agda
module foundation.binary-reflecting-maps-equivalence-relations where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.structure-identity-principle
open import foundation.subtype-identity-principle
open import foundation.universe-levels
```

</details>

## Idea

Consider two types `A` and `B` equipped with equivalence relations `R` and `S`. A binary reflecting map from `A` to `B` to `X` is a binary map `f : A → B → X` such that for any to `R`-related elements `x` and `x'` in `A` and any two `S`-related elements `y` and `y'` in `B` we have `f x y ＝ f x' y'` in `X`.

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {A : UU l1} {B : UU l2}
  (R : Eq-Rel l3 A) (S : Eq-Rel l4 B)
  where

  binary-reflects-Eq-Rel :
    {X : UU l5} (f : A → B → X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflects-Eq-Rel f =
    {x x' : A} {y y' : B} →
    sim-Eq-Rel R x x' → sim-Eq-Rel S y y' → f x y ＝ f x' y'

  binary-reflecting-map-Eq-Rel : (X : UU l5) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  binary-reflecting-map-Eq-Rel X = Σ (A → B → X) binary-reflects-Eq-Rel

  map-binary-reflecting-map-Eq-Rel :
    {X : UU l5} → binary-reflecting-map-Eq-Rel X → A → B → X
  map-binary-reflecting-map-Eq-Rel = pr1

  reflects-binary-reflecting-map-Eq-Rel :
    {X : UU l5} (f : binary-reflecting-map-Eq-Rel X) →
    binary-reflects-Eq-Rel (map-binary-reflecting-map-Eq-Rel f)
  reflects-binary-reflecting-map-Eq-Rel = pr2

  is-prop-binary-reflects-Eq-Rel :
    (X : Set l5) (f : A → B → type-Set X) →
    is-prop (binary-reflects-Eq-Rel f)
  is-prop-binary-reflects-Eq-Rel X f =
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

  binary-reflects-Eq-Rel-Prop :
    (X : Set l5) (f : A → B → type-Set X) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  pr1 (binary-reflects-Eq-Rel-Prop X f) = binary-reflects-Eq-Rel f
  pr2 (binary-reflects-Eq-Rel-Prop X f) = is-prop-binary-reflects-Eq-Rel X f
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
