# Binary functoriality of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.binary-functoriality-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.binary-reflecting-maps-equivalence-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.exponents-set-quotients
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-set-quotients
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

</details>

## Idea

Given three types `A`, `B`, and `C` equipped with equivalence relations `R`, `S`, and `T`, respectively, any binary operation `f : A → B → C` such that for any `x x' : A` such that `R x x'` holds, and for any `y y' : B` such that `S y y'` holds, the relation `T (f x y) (f x' y')` holds extends uniquely to a binary operation `g : A/R → B/S → C/T` such that `g (q x) (q y) = q (f x y)` for all `x : A` and `y : B`.

## Definition

### Binary hom of equivalence relation

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  {C : UU l5} (T : Eq-Rel l6 C)
  where

  preserves-sim-binary-map-Eq-Rel-Prop :
    (A → B → C) → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  preserves-sim-binary-map-Eq-Rel-Prop f =
    Π-Prop' A
      ( λ x →
        Π-Prop' A
          ( λ x' →
            Π-Prop' B
              ( λ y →
                Π-Prop' B
                  ( λ y' →
                    function-Prop
                      ( sim-Eq-Rel R x x')
                      ( function-Prop
                        ( sim-Eq-Rel S y y')
                        ( prop-Eq-Rel T (f x y) (f x' y')))))))

  preserves-sim-binary-map-Eq-Rel :
    (A → B → C) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l6)
  preserves-sim-binary-map-Eq-Rel f =
    type-Prop (preserves-sim-binary-map-Eq-Rel-Prop f)

  is-prop-preserves-sim-binary-map-Eq-Rel :
    (f : A → B → C) → is-prop (preserves-sim-binary-map-Eq-Rel f)
  is-prop-preserves-sim-binary-map-Eq-Rel f =
    is-prop-type-Prop (preserves-sim-binary-map-Eq-Rel-Prop f)

  binary-hom-Eq-Rel : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6)
  binary-hom-Eq-Rel = type-subtype preserves-sim-binary-map-Eq-Rel-Prop

  map-binary-hom-Eq-Rel :
    (f : binary-hom-Eq-Rel) → A → B → C
  map-binary-hom-Eq-Rel = pr1

  preserves-sim-binary-hom-Eq-Rel :
    (f : binary-hom-Eq-Rel) →
    preserves-sim-binary-map-Eq-Rel (map-binary-hom-Eq-Rel f)
  preserves-sim-binary-hom-Eq-Rel = pr2
```

## Properties

### Characterization of equality of `binary-hom-Eq-Rel`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  {C : UU l5} (T : Eq-Rel l6 C)
  where

  binary-htpy-hom-Eq-Rel :
    (f g : binary-hom-Eq-Rel R S T) → UU (l1 ⊔ l3 ⊔ l5)
  binary-htpy-hom-Eq-Rel f g =
    binary-htpy (map-binary-hom-Eq-Rel R S T f) (map-binary-hom-Eq-Rel R S T g)

  refl-binary-htpy-hom-Eq-Rel :
    (f : binary-hom-Eq-Rel R S T) → binary-htpy-hom-Eq-Rel f f
  refl-binary-htpy-hom-Eq-Rel f =
    refl-binary-htpy (map-binary-hom-Eq-Rel R S T f)

  binary-htpy-eq-hom-Eq-Rel :
    (f g : binary-hom-Eq-Rel R S T) → (f ＝ g) → binary-htpy-hom-Eq-Rel f g
  binary-htpy-eq-hom-Eq-Rel f .f refl = refl-binary-htpy-hom-Eq-Rel f

  is-contr-total-binary-htpy-hom-Eq-Rel :
    (f : binary-hom-Eq-Rel R S T) →
    is-contr (Σ (binary-hom-Eq-Rel R S T) (binary-htpy-hom-Eq-Rel f))
  is-contr-total-binary-htpy-hom-Eq-Rel f =
    is-contr-total-Eq-subtype
      ( is-contr-total-binary-htpy (map-binary-hom-Eq-Rel R S T f))
      ( is-prop-preserves-sim-binary-map-Eq-Rel R S T)
      ( map-binary-hom-Eq-Rel R S T f)
      ( refl-binary-htpy-hom-Eq-Rel f)
      ( preserves-sim-binary-hom-Eq-Rel R S T f)

  is-equiv-binary-htpy-eq-hom-Eq-Rel :
    (f g : binary-hom-Eq-Rel R S T) → is-equiv (binary-htpy-eq-hom-Eq-Rel f g)
  is-equiv-binary-htpy-eq-hom-Eq-Rel f =
    fundamental-theorem-id
      ( is-contr-total-binary-htpy-hom-Eq-Rel f)
      ( binary-htpy-eq-hom-Eq-Rel f)

  extensionality-binary-hom-Eq-Rel :
    (f g : binary-hom-Eq-Rel R S T) → (f ＝ g) ≃ binary-htpy-hom-Eq-Rel f g
  pr1 (extensionality-binary-hom-Eq-Rel f g) = binary-htpy-eq-hom-Eq-Rel f g
  pr2 (extensionality-binary-hom-Eq-Rel f g) =
    is-equiv-binary-htpy-eq-hom-Eq-Rel f g

  eq-binary-htpy-hom-Eq-Rel :
    (f g : binary-hom-Eq-Rel R S T) → binary-htpy-hom-Eq-Rel f g → f ＝ g
  eq-binary-htpy-hom-Eq-Rel f g =
    map-inv-equiv (extensionality-binary-hom-Eq-Rel f g)
```

### The type `binary-hom-Eq-Rel R S T` is equivalent to the type `hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T)`

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  {C : UU l5} (T : Eq-Rel l6 C)
  where

  map-hom-binary-hom-Eq-Rel :
    binary-hom-Eq-Rel R S T → A → hom-Eq-Rel S T
  pr1 (map-hom-binary-hom-Eq-Rel f a) = map-binary-hom-Eq-Rel R S T f a
  pr2 (map-hom-binary-hom-Eq-Rel f a) {x} {y} s =
    preserves-sim-binary-hom-Eq-Rel R S T f (refl-Eq-Rel R) s

  preserves-sim-hom-binary-hom-Eq-Rel :
    (f : binary-hom-Eq-Rel R S T) →
    preserves-sim-Eq-Rel R (eq-rel-hom-Eq-Rel S T) (map-hom-binary-hom-Eq-Rel f)
  preserves-sim-hom-binary-hom-Eq-Rel f {x} {y} r b =
    preserves-sim-binary-hom-Eq-Rel R S T f r (refl-Eq-Rel S)

  hom-binary-hom-Eq-Rel :
    binary-hom-Eq-Rel R S T → hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T)
  pr1 (hom-binary-hom-Eq-Rel f) = map-hom-binary-hom-Eq-Rel f
  pr2 (hom-binary-hom-Eq-Rel f) = preserves-sim-hom-binary-hom-Eq-Rel f

  map-binary-hom-hom-Eq-Rel :
    hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T) → A → B → C
  map-binary-hom-hom-Eq-Rel f x =
    map-hom-Eq-Rel S T (map-hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T) f x)

  preserves-sim-binary-hom-hom-Eq-Rel :
    (f : hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T)) →
    preserves-sim-binary-map-Eq-Rel R S T (map-binary-hom-hom-Eq-Rel f)
  preserves-sim-binary-hom-hom-Eq-Rel f {x} {x'} {y} {y'} r s =
    trans-Eq-Rel T
      ( preserves-sim-hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T) f r y)
      ( preserves-sim-hom-Eq-Rel S T
        ( map-hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T) f x')
        ( s))

  binary-hom-hom-Eq-Rel :
    hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T) → binary-hom-Eq-Rel R S T
  pr1 (binary-hom-hom-Eq-Rel f) = map-binary-hom-hom-Eq-Rel f
  pr2 (binary-hom-hom-Eq-Rel f) = preserves-sim-binary-hom-hom-Eq-Rel f

  issec-binary-hom-hom-Eq-Rel :
    ( hom-binary-hom-Eq-Rel ∘ binary-hom-hom-Eq-Rel) ~ id
  issec-binary-hom-hom-Eq-Rel f =
    eq-htpy-hom-Eq-Rel R
      ( eq-rel-hom-Eq-Rel S T)
      ( hom-binary-hom-Eq-Rel (binary-hom-hom-Eq-Rel f))
      ( f)
      ( λ x →
        eq-htpy-hom-Eq-Rel S T
          ( map-hom-Eq-Rel R
            ( eq-rel-hom-Eq-Rel S T)
            ( hom-binary-hom-Eq-Rel (binary-hom-hom-Eq-Rel f))
            ( x))
          ( map-hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T) f x)
          ( refl-htpy))

  isretr-binary-hom-hom-Eq-Rel :
    ( binary-hom-hom-Eq-Rel ∘ hom-binary-hom-Eq-Rel) ~ id
  isretr-binary-hom-hom-Eq-Rel f =
    eq-binary-htpy-hom-Eq-Rel R S T
      ( binary-hom-hom-Eq-Rel (hom-binary-hom-Eq-Rel f))
      ( f)
      ( refl-binary-htpy (map-binary-hom-Eq-Rel R S T f))

  is-equiv-hom-binary-hom-Eq-Rel :
    is-equiv hom-binary-hom-Eq-Rel
  is-equiv-hom-binary-hom-Eq-Rel =
    is-equiv-has-inverse
      binary-hom-hom-Eq-Rel
      issec-binary-hom-hom-Eq-Rel
      isretr-binary-hom-hom-Eq-Rel

  equiv-hom-binary-hom-Eq-Rel :
    binary-hom-Eq-Rel R S T ≃ hom-Eq-Rel R (eq-rel-hom-Eq-Rel S T)
  pr1 equiv-hom-binary-hom-Eq-Rel = hom-binary-hom-Eq-Rel
  pr2 equiv-hom-binary-hom-Eq-Rel = is-equiv-hom-binary-hom-Eq-Rel
```

### Binary functoriality of types that satisfy the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 l9 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (qR : reflecting-map-Eq-Rel R (type-Set QR))
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (qS : reflecting-map-Eq-Rel S (type-Set QS))
  {C : UU l7} (T : Eq-Rel l8 C)
  (QT : Set l9) (qT : reflecting-map-Eq-Rel T (type-Set QT))
  (UqR : {l : Level} → is-set-quotient l R QR qR)
  (UqS : {l : Level} → is-set-quotient l S QS qS)
  (UqT : {l : Level} → is-set-quotient l T QT qT)
  (f : binary-hom-Eq-Rel R S T)
  where

  private
    p : (x : A) (y : B) →
        map-reflecting-map-Eq-Rel T qT (map-binary-hom-Eq-Rel R S T f x y) ＝
        inclusion-is-set-quotient-hom-Eq-Rel S QS qS UqS T QT qT UqT
          ( quotient-hom-Eq-Rel-Set S T)
          ( reflecting-map-quotient-map-hom-Eq-Rel S T)
          ( is-set-quotient-set-quotient-hom-Eq-Rel S T)
          ( quotient-map-hom-Eq-Rel S T (map-hom-binary-hom-Eq-Rel R S T f x))
          ( map-reflecting-map-Eq-Rel S qS y)
    p x y =
      ( inv
        ( coherence-square-map-is-set-quotient S QS qS T QT qT UqS UqT
          ( map-hom-binary-hom-Eq-Rel R S T f x)
          ( y))) ∙
      ( inv
        ( htpy-eq
          ( triangle-inclusion-is-set-quotient-hom-Eq-Rel
            S QS qS UqS T QT qT UqT
            ( quotient-hom-Eq-Rel-Set S T)
            ( reflecting-map-quotient-map-hom-Eq-Rel S T)
            ( is-set-quotient-set-quotient-hom-Eq-Rel S T)
            ( map-hom-binary-hom-Eq-Rel R S T f x))
          ( map-reflecting-map-Eq-Rel S qS y)))

  unique-binary-map-is-set-quotient :
    is-contr
      ( Σ ( type-Set QR → type-Set QS → type-Set QT)
          ( λ h →
            (x : A) (y : B) →
            ( h ( map-reflecting-map-Eq-Rel R qR x)
                ( map-reflecting-map-Eq-Rel S qS y)) ＝
            ( map-reflecting-map-Eq-Rel T qT
              ( map-binary-hom-Eq-Rel R S T f x y))))
  unique-binary-map-is-set-quotient =
    is-contr-equiv
      ( Σ ( type-Set QR → set-quotient-hom-Eq-Rel S T)
          ( λ h →
            ( x : A) →
            ( h (map-reflecting-map-Eq-Rel R qR x)) ＝
            ( quotient-map-hom-Eq-Rel S T
              ( map-hom-binary-hom-Eq-Rel R S T f x))))
      ( equiv-tot
        ( λ h →
          ( equiv-inv-htpy
            ( ( quotient-map-hom-Eq-Rel S T) ∘
              ( map-hom-binary-hom-Eq-Rel R S T f))
            ( h ∘ map-reflecting-map-Eq-Rel R qR))) ∘e
        ( ( inv-equiv
            ( equiv-postcomp-extension-surjection
              ( map-reflecting-map-Eq-Rel R qR ,
                is-surjective-is-set-quotient R QR qR UqR)
              ( ( quotient-map-hom-Eq-Rel S T) ∘
                ( map-hom-binary-hom-Eq-Rel R S T f))
              ( emb-inclusion-is-set-quotient-hom-Eq-Rel S QS qS UqS T QT qT UqT
                ( quotient-hom-Eq-Rel-Set S T)
                ( reflecting-map-quotient-map-hom-Eq-Rel S T)
                ( is-set-quotient-set-quotient-hom-Eq-Rel S T)))) ∘e
          ( equiv-tot
            ( λ h →
              equiv-map-Π
                ( λ x →
                  ( inv-equiv equiv-funext) ∘e
                  ( inv-equiv
                    ( equiv-dependent-universal-property-surj-is-surjective
                      ( map-reflecting-map-Eq-Rel S qS)
                      ( is-surjective-is-set-quotient S QS qS UqS)
                      ( λ u →
                        Id-Prop QT
                        ( inclusion-is-set-quotient-hom-Eq-Rel
                          S QS qS UqS T QT qT UqT
                          ( quotient-hom-Eq-Rel-Set S T)
                          ( reflecting-map-quotient-map-hom-Eq-Rel S T)
                          ( is-set-quotient-set-quotient-hom-Eq-Rel S T)
                          ( quotient-map-hom-Eq-Rel S T
                            ( map-hom-binary-hom-Eq-Rel R S T f x))
                          ( u))
                        ( h (map-reflecting-map-Eq-Rel R qR x) u))) ∘e
                    ( equiv-map-Π
                      ( λ y →
                        ( equiv-inv _ _) ∘e
                        ( equiv-concat'
                          ( h
                            ( map-reflecting-map-Eq-Rel R qR x)
                            ( map-reflecting-map-Eq-Rel S qS y))
                          ( p x y))))))))))
      ( unique-map-is-set-quotient R QR qR
        ( eq-rel-hom-Eq-Rel S T)
        ( quotient-hom-Eq-Rel-Set S T)
        ( reflecting-map-quotient-map-hom-Eq-Rel S T)
        ( UqR)
        ( is-set-quotient-set-quotient-hom-Eq-Rel S T)
        ( hom-binary-hom-Eq-Rel R S T f))

  binary-map-is-set-quotient : type-hom-Set QR (hom-Set QS QT)
  binary-map-is-set-quotient =
    pr1 (center unique-binary-map-is-set-quotient)

  compute-binary-map-is-set-quotient :
    (x : A) (y : B) →
    binary-map-is-set-quotient
      ( map-reflecting-map-Eq-Rel R qR x)
      ( map-reflecting-map-Eq-Rel S qS y) ＝
    map-reflecting-map-Eq-Rel T qT (map-binary-hom-Eq-Rel R S T f x y)
  compute-binary-map-is-set-quotient =
    pr2 (center unique-binary-map-is-set-quotient)
```

### Binary functoriality of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  {C : UU l5} (T : Eq-Rel l6 C)
  (f : binary-hom-Eq-Rel R S T)
  where

  unique-binary-map-set-quotient :
    is-contr
      ( Σ ( set-quotient R → set-quotient S → set-quotient T)
          ( λ h →
            (x : A) (y : B) →
            ( h (quotient-map R x) (quotient-map S y)) ＝
            ( quotient-map T (map-binary-hom-Eq-Rel R S T f x y))))
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
    ( quotient-map T (map-binary-hom-Eq-Rel R S T f x y))
  compute-binary-map-set-quotient =
    pr2 (center unique-binary-map-set-quotient)
```
