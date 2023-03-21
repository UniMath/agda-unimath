# The descent property of the circle

```agda
module synthetic-homotopy-theory.descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.path-algebra
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

The descent property uniquely characterizes type families over the circle.

## Definitions

### Type families over the circle

```agda
Fam-circle :
  ( l1 : Level) → UU (lsuc l1)
Fam-circle l1 = Σ (UU l1) Aut

type-Fam-circle : {l1 : Level} → (P : Fam-circle l1) → UU l1
type-Fam-circle = pr1

aut-Fam-circle : {l1 : Level} → (P : Fam-circle l1) → Aut (type-Fam-circle P)
aut-Fam-circle = pr2
```

## Properties

### Characterization of the identity type of `Fam-circle`

```agda
Eq-Fam-circle :
  { l1 : Level} → Fam-circle l1 → Fam-circle l1 → UU l1
Eq-Fam-circle P Q =
  Σ ( (type-Fam-circle P) ≃ (type-Fam-circle Q))
    ( λ h →
      ( (map-equiv h) ∘ (map-equiv (aut-Fam-circle P))) ~
      ( (map-equiv (aut-Fam-circle Q)) ∘ (map-equiv h)))

refl-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) → Eq-Fam-circle P P
refl-Eq-Fam-circle (X , e) =
  id-equiv , refl-htpy

Eq-eq-Fam-circle :
  { l1 : Level} (P Q : Fam-circle l1) → P ＝ Q → Eq-Fam-circle P Q
Eq-eq-Fam-circle P .P refl = refl-Eq-Fam-circle P

is-contr-total-Eq-Fam-circle :
  { l1 : Level} (P : Fam-circle l1) →
  is-contr (Σ (Fam-circle l1) (Eq-Fam-circle P))
is-contr-total-Eq-Fam-circle (X , e) =
  is-contr-total-Eq-structure
    ( λ Y f h →
      ((map-equiv h) ∘ (map-equiv e)) ~ ((map-equiv f) ∘ (map-equiv h)))
    ( is-contr-total-equiv X)
    ( X , id-equiv)
  ( is-contr-total-htpy-equiv e)

is-equiv-Eq-eq-Fam-circle :
  { l1 : Level} (P Q : Fam-circle l1) → is-equiv (Eq-eq-Fam-circle P Q)
is-equiv-Eq-eq-Fam-circle P =
  fundamental-theorem-id
    ( is-contr-total-Eq-Fam-circle P)
    ( Eq-eq-Fam-circle P)

eq-Eq-Fam-circle :
  { l1 : Level} (P Q : Fam-circle l1) → Eq-Fam-circle P Q → P ＝ Q
eq-Eq-Fam-circle P Q = map-inv-is-equiv (is-equiv-Eq-eq-Fam-circle P Q)
```

### Uniqueness of type families defined by `Fam-circle`

```agda
comparison-Fam-circle :
  ( l1 : Level) → free-loop (UU l1) → Fam-circle l1
comparison-Fam-circle l1 = tot (λ Y → equiv-eq)

is-equiv-comparison-Fam-circle :
  ( l1 : Level) → is-equiv (comparison-Fam-circle l1)
is-equiv-comparison-Fam-circle l1 =
  is-equiv-tot-is-fiberwise-equiv (λ Y → univalence Y Y)

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  where

  ev-Fam-circle : ( X → UU l2) → Fam-circle l2
  pr1 (ev-Fam-circle P) = P (base-free-loop l)
  pr2 (ev-Fam-circle P) = equiv-tr P (loop-free-loop l)

  triangle-comparison-Fam-circle :
    ev-Fam-circle ~ ((comparison-Fam-circle l2) ∘ (ev-free-loop l (UU l2)))
  triangle-comparison-Fam-circle P =
    eq-Eq-Fam-circle
      ( ev-Fam-circle P)
      ( comparison-Fam-circle _ (ev-free-loop l (UU _) P))
      ( id-equiv , (htpy-eq (inv (tr-equiv-eq-ap (loop-free-loop l)))))

  is-equiv-ev-Fam-circle-universal-property-circle :
    ( up-circle : universal-property-circle (lsuc l2) l) →
    is-equiv ev-Fam-circle
  is-equiv-ev-Fam-circle-universal-property-circle up-circle =
     is-equiv-comp-htpy
      ( ev-Fam-circle)
      ( comparison-Fam-circle l2)
      ( ev-free-loop l (UU l2))
      ( triangle-comparison-Fam-circle)
      ( up-circle (UU l2))
      ( is-equiv-comparison-Fam-circle l2)

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loop X) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {X} l =
  ( Q : Fam-circle l2) →
    is-contr (Σ (X → UU l2) (λ P → Eq-Fam-circle Q (ev-Fam-circle l P)))

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  where

  unique-family-property-universal-property-circle :
    universal-property-circle (lsuc l2) l → unique-family-property-circle l2 l
  unique-family-property-universal-property-circle up-circle Q =
    is-contr-is-equiv'
      ( fib (ev-Fam-circle l) Q)
      ( tot (λ P → Eq-eq-Fam-circle Q (ev-Fam-circle l P) ∘ inv))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ P →
          is-equiv-comp _ _
            ( is-equiv-inv _ _)
            ( is-equiv-Eq-eq-Fam-circle Q (ev-Fam-circle l P))))
      ( is-contr-map-is-equiv
        ( is-equiv-ev-Fam-circle-universal-property-circle l up-circle)
        ( Q))
```

### Sections of families over the circle are exactly the fixed points of the associated automorphism

```agda
module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : Fam-circle l2) (αβ : Eq-Fam-circle P (ev-Fam-circle l Q))
  where

  private
    α : type-Fam-circle P ≃ Q (base-free-loop l)
    α = pr1 αβ

  map-path-over-loop-fib-aut-Fam-circle :
    (x y : type-Fam-circle P) → (map-equiv (aut-Fam-circle P) x ＝ y ) →
    ( path-over Q (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  map-path-over-loop-fib-aut-Fam-circle x y q =
    inv (pr2 αβ _) ∙ (ap (map-equiv α) q)

  is-equiv-map-path-over-loop-fib-aut-Fam-circle :
    ( x y : type-Fam-circle P) →
    is-equiv (map-path-over-loop-fib-aut-Fam-circle x y)
  is-equiv-map-path-over-loop-fib-aut-Fam-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fib (map-equiv α) _)
        ( equiv-fib _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv α)
          ( _)))
      ( map-path-over-loop-fib-aut-Fam-circle x)
      ( _)

  equiv-path-over-loop-fib-aut-Fam-circle :
    (x y : type-Fam-circle P) →
    (map-equiv (aut-Fam-circle P) x ＝ y) ≃
    (path-over Q (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  pr1 (equiv-path-over-loop-fib-aut-Fam-circle x y) =
    map-path-over-loop-fib-aut-Fam-circle x y
  pr2 (equiv-path-over-loop-fib-aut-Fam-circle x y) =
    is-equiv-map-path-over-loop-fib-aut-Fam-circle x y
```

```agda
Section-Fam-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X) (P : Fam-circle l2) → UU _
Section-Fam-circle l P =
  Σ (type-Fam-circle P) (λ p → (map-equiv (aut-Fam-circle P) p) ＝ p)

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : Fam-circle l2)
  ( αβ : Eq-Fam-circle P (ev-Fam-circle l Q))
  where

  private
    α : type-Fam-circle P ≃ Q (base-free-loop l)
    α = pr1 αβ

  ev-Section-Fam-circle :
    ( (x : X) → Q x) → Section-Fam-circle l P
  pr1 (ev-Section-Fam-circle s) =
    map-inv-equiv
      ( α)
      ( s (base-free-loop l))
  pr2 (ev-Section-Fam-circle s) =
    map-inv-is-equiv
      ( is-equiv-map-path-over-loop-fib-aut-Fam-circle l Q P αβ _ _)
      ( ( ap (tr Q (loop-free-loop l)) (issec-map-inv-equiv α _)) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv (issec-map-inv-equiv α _))))

  equiv-Section-Fam-circle-free-dependent-loop :
    Section-Fam-circle l P ≃ free-dependent-loop l Q
  equiv-Section-Fam-circle-free-dependent-loop =
    equiv-Σ _ α (λ x → equiv-path-over-loop-fib-aut-Fam-circle l Q P αβ x x)

  comparison-Section-Fam-circle :
    Section-Fam-circle l P → free-dependent-loop l Q
  comparison-Section-Fam-circle =
    map-equiv equiv-Section-Fam-circle-free-dependent-loop

  triangle-comparison-Section-Fam-circle :
    ( ev-free-loop-Π l Q) ~
    ( comparison-Section-Fam-circle ∘ ev-Section-Fam-circle)
  triangle-comparison-Section-Fam-circle s =
    eq-Eq-free-dependent-loop l Q
      ( ev-free-loop-Π l Q s)
      ( ( comparison-Section-Fam-circle ∘ ev-Section-Fam-circle) s)
      ( inv issec-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl {x = ap _ (inv issec-inv-α)})
            ( issec-map-inv-is-equiv
              ( is-equiv-map-path-over-loop-fib-aut-Fam-circle l Q P αβ _ _)
              ( _))) ∙
          ( ( inv (assoc (ap _ (inv issec-inv-α)) _ _)) ∙
            ( horizontal-concat-Id²
              ( inv
                ( ap-concat-eq _
                  ( inv issec-inv-α)
                  ( issec-inv-α)
                  ( refl)
                  ( inv (left-inv issec-inv-α))))
              ( refl)))))
    where
    issec-inv-α : eq-value (map-equiv α ∘ map-inv-equiv α) id (s (base-free-loop l))
    issec-inv-α = issec-map-inv-equiv α _

  is-equiv-comparison-Section-Fam-circle :
    is-equiv comparison-Section-Fam-circle
  is-equiv-comparison-Section-Fam-circle =
    is-equiv-map-equiv equiv-Section-Fam-circle-free-dependent-loop

  is-equiv-ev-Section-Fam-circle :
    (dependent-universal-property-circle l2 l) →
    is-equiv ev-Section-Fam-circle
  is-equiv-ev-Section-Fam-circle dup =
    is-equiv-right-factor-htpy
      ( ev-free-loop-Π l Q)
      ( comparison-Section-Fam-circle)
      ( ev-Section-Fam-circle)
      ( triangle-comparison-Section-Fam-circle)
      ( is-equiv-comparison-Section-Fam-circle)
      ( dup Q)

  equiv-ev-Section-Fam-circle :
    (dependent-universal-property-circle l2 l) →
    ((x : X) → Q x) ≃ (Section-Fam-circle l P)
  pr1 (equiv-ev-Section-Fam-circle dup) = ev-Section-Fam-circle
  pr2 (equiv-ev-Section-Fam-circle dup) = is-equiv-ev-Section-Fam-circle dup

  compute-ev-Section-Fam-circle :
    ( pr1 ∘ ev-Section-Fam-circle ) ~
    ( (map-inv-equiv α) ∘ (ev-pt (base-free-loop l) _))
  compute-ev-Section-Fam-circle = refl-htpy
