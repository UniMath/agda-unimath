# Binary functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.binary-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.exponents-set-quotients
open import foundation.function-extensionality
open import foundation.functoriality-set-quotients
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalence-relations
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.propositions
open import foundation-core.subtypes
```

</details>

## Idea

Given three types `A`, `B`, and `C` equipped with equivalence relations `R`,
`S`, and `T`, respectively, any binary operation `f : A → B → C` such that for
any `x x' : A` such that `R x x'` holds, and for any `y y' : B` such that
`S y y'` holds, the relation `T (f x y) (f x' y')` holds extends uniquely to a
binary operation `g : A/R → B/S → C/T` such that `g (q x) (q y) = q (f x y)` for
all `x : A` and `y : B`.

## Definition

### Binary hom of equivalence relation

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  {C : UU l5} (T : Equivalence-Relation l6 C)
  where

  preserves-sim-binary-map-Equivalence-Relation-Prop :
    (A → B → C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  preserves-sim-binary-map-Equivalence-Relation-Prop f =
    Π-Prop' A
      ( λ x →
        Π-Prop' A
          ( λ x' →
            Π-Prop' B
              ( λ y →
                Π-Prop' B
                  ( λ y' →
                    function-Prop
                      ( sim-Equivalence-Relation R x x')
                      ( function-Prop
                        ( sim-Equivalence-Relation S y y')
                        ( prop-Equivalence-Relation T (f x y) (f x' y')))))))

  preserves-sim-binary-map-Equivalence-Relation :
    (A → B → C) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  preserves-sim-binary-map-Equivalence-Relation f =
    type-Prop (preserves-sim-binary-map-Equivalence-Relation-Prop f)

  is-prop-preserves-sim-binary-map-Equivalence-Relation :
    (f : A → B → C) → is-prop (preserves-sim-binary-map-Equivalence-Relation f)
  is-prop-preserves-sim-binary-map-Equivalence-Relation f =
    is-prop-type-Prop (preserves-sim-binary-map-Equivalence-Relation-Prop f)

  binary-hom-Equivalence-Relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  binary-hom-Equivalence-Relation =
    type-subtype preserves-sim-binary-map-Equivalence-Relation-Prop

  map-binary-hom-Equivalence-Relation :
    (f : binary-hom-Equivalence-Relation) → A → B → C
  map-binary-hom-Equivalence-Relation = pr1

  preserves-sim-binary-hom-Equivalence-Relation :
    (f : binary-hom-Equivalence-Relation) →
    preserves-sim-binary-map-Equivalence-Relation
      ( map-binary-hom-Equivalence-Relation f)
  preserves-sim-binary-hom-Equivalence-Relation = pr2
```

## Properties

### Characterization of equality of `binary-hom-Equivalence-Relation`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  {C : UU l5} (T : Equivalence-Relation l6 C)
  where

  binary-htpy-hom-Equivalence-Relation :
    (f g : binary-hom-Equivalence-Relation R S T) → UU (l1 ⊔ l3 ⊔ l5)
  binary-htpy-hom-Equivalence-Relation f g =
    binary-htpy
      ( map-binary-hom-Equivalence-Relation R S T f)
      ( map-binary-hom-Equivalence-Relation R S T g)

  refl-binary-htpy-hom-Equivalence-Relation :
    (f : binary-hom-Equivalence-Relation R S T) →
    binary-htpy-hom-Equivalence-Relation f f
  refl-binary-htpy-hom-Equivalence-Relation f =
    refl-binary-htpy (map-binary-hom-Equivalence-Relation R S T f)

  binary-htpy-eq-hom-Equivalence-Relation :
    (f g : binary-hom-Equivalence-Relation R S T) →
    (f ＝ g) → binary-htpy-hom-Equivalence-Relation f g
  binary-htpy-eq-hom-Equivalence-Relation f .f refl =
    refl-binary-htpy-hom-Equivalence-Relation f

  is-contr-total-binary-htpy-hom-Equivalence-Relation :
    (f : binary-hom-Equivalence-Relation R S T) →
    is-contr
      ( Σ
        ( binary-hom-Equivalence-Relation R S T)
        ( binary-htpy-hom-Equivalence-Relation f))
  is-contr-total-binary-htpy-hom-Equivalence-Relation f =
    is-contr-total-Eq-subtype
      ( is-contr-total-binary-htpy
        ( map-binary-hom-Equivalence-Relation R S T f))
      ( is-prop-preserves-sim-binary-map-Equivalence-Relation R S T)
      ( map-binary-hom-Equivalence-Relation R S T f)
      ( refl-binary-htpy-hom-Equivalence-Relation f)
      ( preserves-sim-binary-hom-Equivalence-Relation R S T f)

  is-equiv-binary-htpy-eq-hom-Equivalence-Relation :
    (f g : binary-hom-Equivalence-Relation R S T) →
    is-equiv (binary-htpy-eq-hom-Equivalence-Relation f g)
  is-equiv-binary-htpy-eq-hom-Equivalence-Relation f =
    fundamental-theorem-id
      ( is-contr-total-binary-htpy-hom-Equivalence-Relation f)
      ( binary-htpy-eq-hom-Equivalence-Relation f)

  extensionality-binary-hom-Equivalence-Relation :
    (f g : binary-hom-Equivalence-Relation R S T) →
    (f ＝ g) ≃ binary-htpy-hom-Equivalence-Relation f g
  pr1 (extensionality-binary-hom-Equivalence-Relation f g) =
    binary-htpy-eq-hom-Equivalence-Relation f g
  pr2 (extensionality-binary-hom-Equivalence-Relation f g) =
    is-equiv-binary-htpy-eq-hom-Equivalence-Relation f g

  eq-binary-htpy-hom-Equivalence-Relation :
    (f g : binary-hom-Equivalence-Relation R S T) →
    binary-htpy-hom-Equivalence-Relation f g → f ＝ g
  eq-binary-htpy-hom-Equivalence-Relation f g =
    map-inv-equiv (extensionality-binary-hom-Equivalence-Relation f g)
```

### The type `binary-hom-Equivalence-Relation R S T` is equivalent to the type `hom-Equivalence-Relation R (eq-rel-hom-Equivalence-Relation S T)`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  {C : UU l5} (T : Equivalence-Relation l6 C)
  where

  map-hom-binary-hom-Equivalence-Relation :
    binary-hom-Equivalence-Relation R S T → A → hom-Equivalence-Relation S T
  pr1 (map-hom-binary-hom-Equivalence-Relation f a) =
    map-binary-hom-Equivalence-Relation R S T f a
  pr2 (map-hom-binary-hom-Equivalence-Relation f a) {x} {y} =
    preserves-sim-binary-hom-Equivalence-Relation R S T f
      ( refl-Equivalence-Relation R a)

  preserves-sim-hom-binary-hom-Equivalence-Relation :
    (f : binary-hom-Equivalence-Relation R S T) →
    preserves-sim-Equivalence-Relation R
      ( eq-rel-hom-Equivalence-Relation S T)
      ( map-hom-binary-hom-Equivalence-Relation f)
  preserves-sim-hom-binary-hom-Equivalence-Relation f r b =
    preserves-sim-binary-hom-Equivalence-Relation R S T f r
      ( refl-Equivalence-Relation S b)

  hom-binary-hom-Equivalence-Relation :
    binary-hom-Equivalence-Relation R S T →
    hom-Equivalence-Relation R (eq-rel-hom-Equivalence-Relation S T)
  pr1 (hom-binary-hom-Equivalence-Relation f) =
    map-hom-binary-hom-Equivalence-Relation f
  pr2 (hom-binary-hom-Equivalence-Relation f) =
    preserves-sim-hom-binary-hom-Equivalence-Relation f

  map-binary-hom-hom-Equivalence-Relation :
    hom-Equivalence-Relation R (eq-rel-hom-Equivalence-Relation S T) →
    A → B → C
  map-binary-hom-hom-Equivalence-Relation f x =
    map-hom-Equivalence-Relation S T
      ( map-hom-Equivalence-Relation R
        ( eq-rel-hom-Equivalence-Relation S T)
        ( f)
        ( x))

  preserves-sim-binary-hom-hom-Equivalence-Relation :
    (f : hom-Equivalence-Relation R (eq-rel-hom-Equivalence-Relation S T)) →
    preserves-sim-binary-map-Equivalence-Relation R S T
      ( map-binary-hom-hom-Equivalence-Relation f)
  preserves-sim-binary-hom-hom-Equivalence-Relation f {x} {x'} {y} {y'} r s =
    transitive-Equivalence-Relation T
      ( pr1
        ( map-hom-Equivalence-Relation
            R (eq-rel-hom-Equivalence-Relation S T) f x)
        ( y))
      ( pr1
        ( map-hom-Equivalence-Relation
            R (eq-rel-hom-Equivalence-Relation S T) f x') y)
      ( map-hom-Equivalence-Relation S T (pr1 f x') y')
      ( preserves-sim-hom-Equivalence-Relation S T
        ( map-hom-Equivalence-Relation
            R (eq-rel-hom-Equivalence-Relation S T) f x')
        ( s))
      ( preserves-sim-hom-Equivalence-Relation
          R (eq-rel-hom-Equivalence-Relation S T) f r y)

  binary-hom-hom-Equivalence-Relation :
    hom-Equivalence-Relation R (eq-rel-hom-Equivalence-Relation S T) →
    binary-hom-Equivalence-Relation R S T
  pr1 (binary-hom-hom-Equivalence-Relation f) =
    map-binary-hom-hom-Equivalence-Relation f
  pr2 (binary-hom-hom-Equivalence-Relation f) =
    preserves-sim-binary-hom-hom-Equivalence-Relation f

  is-section-binary-hom-hom-Equivalence-Relation :
    ( hom-binary-hom-Equivalence-Relation ∘
      binary-hom-hom-Equivalence-Relation) ~
    id
  is-section-binary-hom-hom-Equivalence-Relation f =
    eq-htpy-hom-Equivalence-Relation R
      ( eq-rel-hom-Equivalence-Relation S T)
      ( hom-binary-hom-Equivalence-Relation
        ( binary-hom-hom-Equivalence-Relation f))
      ( f)
      ( λ x →
        eq-htpy-hom-Equivalence-Relation S T
          ( map-hom-Equivalence-Relation R
            ( eq-rel-hom-Equivalence-Relation S T)
            ( hom-binary-hom-Equivalence-Relation
              ( binary-hom-hom-Equivalence-Relation f))
            ( x))
          ( map-hom-Equivalence-Relation
              R (eq-rel-hom-Equivalence-Relation S T) f x)
          ( refl-htpy))

  is-retraction-binary-hom-hom-Equivalence-Relation :
    ( binary-hom-hom-Equivalence-Relation ∘
      hom-binary-hom-Equivalence-Relation) ~
    id
  is-retraction-binary-hom-hom-Equivalence-Relation f =
    eq-binary-htpy-hom-Equivalence-Relation R S T
      ( binary-hom-hom-Equivalence-Relation
        ( hom-binary-hom-Equivalence-Relation f))
      ( f)
      ( refl-binary-htpy (map-binary-hom-Equivalence-Relation R S T f))

  is-equiv-hom-binary-hom-Equivalence-Relation :
    is-equiv hom-binary-hom-Equivalence-Relation
  is-equiv-hom-binary-hom-Equivalence-Relation =
    is-equiv-has-inverse
      binary-hom-hom-Equivalence-Relation
      is-section-binary-hom-hom-Equivalence-Relation
      is-retraction-binary-hom-hom-Equivalence-Relation

  equiv-hom-binary-hom-Equivalence-Relation :
    binary-hom-Equivalence-Relation R S T ≃
    hom-Equivalence-Relation R (eq-rel-hom-Equivalence-Relation S T)
  pr1 equiv-hom-binary-hom-Equivalence-Relation =
    hom-binary-hom-Equivalence-Relation
  pr2 equiv-hom-binary-hom-Equivalence-Relation =
    is-equiv-hom-binary-hom-Equivalence-Relation
```

### Binary functoriality of types that satisfy the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  (QR : Set l3) (qR : reflecting-map-Equivalence-Relation R (type-Set QR))
  {B : UU l4} (S : Equivalence-Relation l5 B)
  (QS : Set l6) (qS : reflecting-map-Equivalence-Relation S (type-Set QS))
  {C : UU l7} (T : Equivalence-Relation l8 C)
  (QT : Set l9) (qT : reflecting-map-Equivalence-Relation T (type-Set QT))
  (UqR : {l : Level} → is-set-quotient l R QR qR)
  (UqS : {l : Level} → is-set-quotient l S QS qS)
  (UqT : {l : Level} → is-set-quotient l T QT qT)
  (f : binary-hom-Equivalence-Relation R S T)
  where

  private
    p :
      (x : A) (y : B) →
      map-reflecting-map-Equivalence-Relation T qT
        ( map-binary-hom-Equivalence-Relation R S T f x y) ＝
      inclusion-is-set-quotient-hom-Equivalence-Relation S QS qS UqS T QT qT UqT
        ( quotient-hom-Equivalence-Relation-Set S T)
        ( reflecting-map-quotient-map-hom-Equivalence-Relation S T)
        ( is-set-quotient-set-quotient-hom-Equivalence-Relation S T)
        ( quotient-map-hom-Equivalence-Relation S T
          ( map-hom-binary-hom-Equivalence-Relation R S T f x))
        ( map-reflecting-map-Equivalence-Relation S qS y)
    p x y =
      ( inv
        ( coherence-square-map-is-set-quotient S QS qS T QT qT UqS UqT
          ( map-hom-binary-hom-Equivalence-Relation R S T f x)
          ( y))) ∙
      ( inv
        ( htpy-eq
          ( triangle-inclusion-is-set-quotient-hom-Equivalence-Relation
            S QS qS UqS T QT qT UqT
            ( quotient-hom-Equivalence-Relation-Set S T)
            ( reflecting-map-quotient-map-hom-Equivalence-Relation S T)
            ( is-set-quotient-set-quotient-hom-Equivalence-Relation S T)
            ( map-hom-binary-hom-Equivalence-Relation R S T f x))
          ( map-reflecting-map-Equivalence-Relation S qS y)))

  unique-binary-map-is-set-quotient :
    is-contr
      ( Σ ( type-Set QR → type-Set QS → type-Set QT)
          ( λ h →
            (x : A) (y : B) →
            ( h ( map-reflecting-map-Equivalence-Relation R qR x)
                ( map-reflecting-map-Equivalence-Relation S qS y)) ＝
            ( map-reflecting-map-Equivalence-Relation T qT
              ( map-binary-hom-Equivalence-Relation R S T f x y))))
  unique-binary-map-is-set-quotient =
    is-contr-equiv
      ( Σ ( type-Set QR → set-quotient-hom-Equivalence-Relation S T)
          ( λ h →
            ( x : A) →
            ( h (map-reflecting-map-Equivalence-Relation R qR x)) ＝
            ( quotient-map-hom-Equivalence-Relation S T
              ( map-hom-binary-hom-Equivalence-Relation R S T f x))))
      ( equiv-tot
        ( λ h →
          ( equiv-inv-htpy
            ( ( quotient-map-hom-Equivalence-Relation S T) ∘
              ( map-hom-binary-hom-Equivalence-Relation R S T f))
            ( h ∘ map-reflecting-map-Equivalence-Relation R qR))) ∘e
        ( ( inv-equiv
            ( equiv-postcomp-extension-surjection
              ( map-reflecting-map-Equivalence-Relation R qR ,
                is-surjective-is-set-quotient R QR qR UqR)
              ( ( quotient-map-hom-Equivalence-Relation S T) ∘
                ( map-hom-binary-hom-Equivalence-Relation R S T f))
              ( emb-inclusion-is-set-quotient-hom-Equivalence-Relation
                S QS qS UqS T QT qT UqT
                ( quotient-hom-Equivalence-Relation-Set S T)
                ( reflecting-map-quotient-map-hom-Equivalence-Relation S T)
                ( is-set-quotient-set-quotient-hom-Equivalence-Relation
                    S T)))) ∘e
          ( equiv-tot
            ( λ h →
              equiv-map-Π
                ( λ x →
                  ( inv-equiv equiv-funext) ∘e
                  ( inv-equiv
                    ( equiv-dependent-universal-property-surj-is-surjective
                      ( map-reflecting-map-Equivalence-Relation S qS)
                      ( is-surjective-is-set-quotient S QS qS UqS)
                      ( λ u →
                        Id-Prop QT
                        ( inclusion-is-set-quotient-hom-Equivalence-Relation
                          S QS qS UqS T QT qT UqT
                          ( quotient-hom-Equivalence-Relation-Set S T)
                          ( reflecting-map-quotient-map-hom-Equivalence-Relation
                              S T)
                          ( is-set-quotient-set-quotient-hom-Equivalence-Relation
                              S T)
                          ( quotient-map-hom-Equivalence-Relation S T
                            ( map-hom-binary-hom-Equivalence-Relation
                                R S T f x))
                          ( u))
                        ( h
                          ( map-reflecting-map-Equivalence-Relation R qR x)
                          ( u)))) ∘e
                    ( equiv-map-Π
                      ( λ y →
                        ( equiv-inv _ _) ∘e
                        ( equiv-concat'
                          ( h
                            ( map-reflecting-map-Equivalence-Relation R qR x)
                            ( map-reflecting-map-Equivalence-Relation S qS y))
                          ( p x y))))))))))
      ( unique-map-is-set-quotient R QR qR
        ( eq-rel-hom-Equivalence-Relation S T)
        ( quotient-hom-Equivalence-Relation-Set S T)
        ( reflecting-map-quotient-map-hom-Equivalence-Relation S T)
        ( UqR)
        ( is-set-quotient-set-quotient-hom-Equivalence-Relation S T)
        ( hom-binary-hom-Equivalence-Relation R S T f))

  binary-map-is-set-quotient : type-hom-Set QR (hom-Set QS QT)
  binary-map-is-set-quotient =
    pr1 (center unique-binary-map-is-set-quotient)

  compute-binary-map-is-set-quotient :
    (x : A) (y : B) →
    binary-map-is-set-quotient
      ( map-reflecting-map-Equivalence-Relation R qR x)
      ( map-reflecting-map-Equivalence-Relation S qS y) ＝
    map-reflecting-map-Equivalence-Relation
      T qT (map-binary-hom-Equivalence-Relation R S T f x y)
  compute-binary-map-is-set-quotient =
    pr2 (center unique-binary-map-is-set-quotient)
```

### Binary functoriality of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  {C : UU l5} (T : Equivalence-Relation l6 C)
  (f : binary-hom-Equivalence-Relation R S T)
  where

  unique-binary-map-set-quotient :
    is-contr
      ( Σ ( set-quotient R → set-quotient S → set-quotient T)
          ( λ h →
            (x : A) (y : B) →
            ( h (quotient-map R x) (quotient-map S y)) ＝
            ( quotient-map T
              ( map-binary-hom-Equivalence-Relation R S T f x y))))
  unique-binary-map-set-quotient =
    unique-binary-map-is-set-quotient
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( T)
      ( quotient-Set T)
      ( reflecting-map-quotient-map T)
      ( is-set-quotient-set-quotient R)
      ( is-set-quotient-set-quotient S)
      ( is-set-quotient-set-quotient T)
      ( f)

  binary-map-set-quotient : set-quotient R → set-quotient S → set-quotient T
  binary-map-set-quotient =
    pr1 (center unique-binary-map-set-quotient)

  compute-binary-map-set-quotient :
    (x : A) (y : B) →
    ( binary-map-set-quotient (quotient-map R x) (quotient-map S y)) ＝
    ( quotient-map T (map-binary-hom-Equivalence-Relation R S T f x y))
  compute-binary-map-set-quotient =
    pr2 (center unique-binary-map-set-quotient)
```
