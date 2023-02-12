---
title: Binary functoriality of set quotients
---

```agda
module foundation.binary-functoriality-set-quotients where

open import foundation.binary-homotopies
open import foundation.binary-reflecting-maps-equivalence-relations
open import foundation.contractible-types
open import foundation.dependent-pair-types
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
open import foundation.sets
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

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
  where

  right-extension-is-set-quotient-binary-reflecting-map-Eq-Rel :
    ({l : Level} → is-set-quotient l S QS qS) →
    ({l : Level} → is-set-quotient l T QT qT) →
    binary-hom-Eq-Rel R S T →
    reflecting-map-Eq-Rel R (type-hom-Set QS QT)
  right-extension-is-set-quotient-binary-reflecting-map-Eq-Rel UqS UqT f =
    comp-reflecting-map-Eq-Rel R
      ( eq-rel-hom-Eq-Rel S T)
      ( universal-reflecting-map-is-set-quotient-hom-Eq-Rel
        S QS qS UqS T QT qT UqT)
      ( hom-binary-hom-Eq-Rel R S T f)

--   unique-binary-map-set-quotient :
--     ({l : Level} → is-set-quotient l R QR qR) →
--     ({l : Level} → is-set-quotient l S QS qS) →
--     ({l : Level} → is-set-quotient l T QT qT) →
--     (f : binary-hom-Eq-Rel R S T) →
--     is-contr
--       ( Σ ( type-Set QR → type-Set QS → type-Set QT)
--           ( λ h →
--             (x : A) (y : B) →
--             ( h ( map-reflecting-map-Eq-Rel R qR x)
--                 ( map-reflecting-map-Eq-Rel S qS y)) ＝
--             ( map-reflecting-map-Eq-Rel T qT
--               ( map-binary-hom-Eq-Rel R S T f x y))))
--   unique-binary-map-set-quotient UqR UqS UqT f =
--     is-contr-equiv'
--       ( Σ ( type-Set QR → type-Set QS → type-Set QT)
--           ( λ h →
--             (x : A) →
--             ( h ( map-reflecting-map-Eq-Rel R qR x)) ＝
--             ( map-universal-property-set-quotient-is-set-quotient
--               S QS qS UqS QT
--               ( comp-reflecting-map-Eq-Rel S T qT
--                 ( map-hom-binary-hom-Eq-Rel R S T f x)))))
--       ( equiv-tot
--         ( λ μ →
--           equiv-map-Π
--             ( λ x →
--               {!!} ∘e
--               ( equiv-funext))))
--       ( universal-property-set-quotient-is-set-quotient R QR qR UqR
--         ( {!!}) {!!})

-- ```

-- ### Binary functoriality of set quotients


