# The descent property of the circle

```agda
module synthetic-homotopy-theory.descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.automorphisms
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.path-algebra
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.free-loops
open import synthetic-homotopy-theory.universal-property-circle
```

</details>

## Idea

The descent property uniquely characterizes type families over the circle.

## Definitions

### Descent data for the circle

```agda
Descent-data-circle :
  ( l1 : Level) → UU (lsuc l1)
Descent-data-circle l1 = Σ (UU l1) Aut

module _
  { l1 : Level} (P : Descent-data-circle l1)
  where

  type-Descent-data-circle : UU l1
  type-Descent-data-circle = pr1 P

  aut-Descent-data-circle : Aut type-Descent-data-circle
  aut-Descent-data-circle = pr2 P
```

### Fixpoints of the descent data

```agda
fixpoint-Descent-data-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( P : Descent-data-circle l2) → UU _
fixpoint-Descent-data-circle l P =
  Σ ( type-Descent-data-circle P)
    ( λ p → (map-equiv (aut-Descent-data-circle P) p) ＝ p)
```

### Homomorphisms between descent data for the circle

```agda
hom-Descent-data-circle :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  ( P : Descent-data-circle l2) (Q : Descent-data-circle l3) →
  UU (l2 ⊔ l3)
hom-Descent-data-circle _ (Y , e) (Z , f) =
  Σ ( Y → Z)
    ( λ h → (h ∘ (map-equiv e)) ~ ((map-equiv f) ∘ h))
```

## Properties

### Characterization of the identity type of descent data for the circle

```agda
Eq-Descent-data-circle :
  { l1 : Level} → Descent-data-circle l1 → Descent-data-circle l1 →
  UU l1
Eq-Descent-data-circle P Q =
  Σ ( (type-Descent-data-circle P) ≃ (type-Descent-data-circle Q))
    ( λ h →
      ( (map-equiv h) ∘ (map-equiv (aut-Descent-data-circle P))) ~
      ( (map-equiv (aut-Descent-data-circle Q)) ∘ (map-equiv h)))

refl-Eq-Descent-data-circle :
  { l1 : Level} (P : Descent-data-circle l1) →
  Eq-Descent-data-circle P P
refl-Eq-Descent-data-circle (X , e) = id-equiv , refl-htpy

Eq-eq-Descent-data-circle :
  { l1 : Level} (P Q : Descent-data-circle l1) →
  P ＝ Q → Eq-Descent-data-circle P Q
Eq-eq-Descent-data-circle P .P refl = refl-Eq-Descent-data-circle P

is-contr-total-Eq-Descent-data-circle :
  { l1 : Level} (P : Descent-data-circle l1) →
  is-contr (Σ (Descent-data-circle l1) (Eq-Descent-data-circle P))
is-contr-total-Eq-Descent-data-circle (X , e) =
  is-contr-total-Eq-structure
    ( λ Y f h →
      ((map-equiv h) ∘ (map-equiv e)) ~ ((map-equiv f) ∘ (map-equiv h)))
    ( is-contr-total-equiv X)
    ( X , id-equiv)
  ( is-contr-total-htpy-equiv e)

is-equiv-Eq-eq-Descent-data-circle :
  { l1 : Level} (P Q : Descent-data-circle l1) →
  is-equiv (Eq-eq-Descent-data-circle P Q)
is-equiv-Eq-eq-Descent-data-circle P =
  fundamental-theorem-id
    ( is-contr-total-Eq-Descent-data-circle P)
    ( Eq-eq-Descent-data-circle P)

eq-Eq-Descent-data-circle :
  { l1 : Level} (P Q : Descent-data-circle l1) →
  Eq-Descent-data-circle P Q → P ＝ Q
eq-Eq-Descent-data-circle P Q =
  map-inv-is-equiv (is-equiv-Eq-eq-Descent-data-circle P Q)
```

### Uniqueness of descent data characterizing a particular type family over the circle

```agda
comparison-Descent-data-circle :
  ( l1 : Level) → free-loop (UU l1) → Descent-data-circle l1
comparison-Descent-data-circle l1 = tot (λ Y → equiv-eq)

is-equiv-comparison-Descent-data-circle :
  ( l1 : Level) → is-equiv (comparison-Descent-data-circle l1)
is-equiv-comparison-Descent-data-circle l1 =
  is-equiv-tot-is-fiberwise-equiv (λ Y → univalence Y Y)

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  where

  ev-Descent-data-circle : (X → UU l2) → Descent-data-circle l2
  pr1 (ev-Descent-data-circle P) = P (base-free-loop l)
  pr2 (ev-Descent-data-circle P) = equiv-tr P (loop-free-loop l)

  triangle-comparison-Descent-data-circle :
    ev-Descent-data-circle ~
    ( (comparison-Descent-data-circle l2) ∘ (ev-free-loop l (UU l2)))
  triangle-comparison-Descent-data-circle P =
    eq-Eq-Descent-data-circle
      ( ev-Descent-data-circle P)
      ( comparison-Descent-data-circle _ (ev-free-loop l (UU l2) P))
      ( id-equiv , (htpy-eq (inv (tr-equiv-eq-ap (loop-free-loop l)))))

  is-equiv-ev-Descent-data-circle-universal-property-circle :
    ( up-circle : universal-property-circle (lsuc l2) l) →
    is-equiv ev-Descent-data-circle
  is-equiv-ev-Descent-data-circle-universal-property-circle up-circle =
     is-equiv-comp-htpy
      ( ev-Descent-data-circle)
      ( comparison-Descent-data-circle l2)
      ( ev-free-loop l (UU l2))
      ( triangle-comparison-Descent-data-circle)
      ( up-circle (UU l2))
      ( is-equiv-comparison-Descent-data-circle l2)

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loop X) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {X} l =
  ( Q : Descent-data-circle l2) →
    is-contr
    ( Σ (X → UU l2)
        (λ P → Eq-Descent-data-circle Q (ev-Descent-data-circle l P)))

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  where

  unique-family-property-universal-property-circle :
    universal-property-circle (lsuc l2) l →
    unique-family-property-circle l2 l
  unique-family-property-universal-property-circle up-circle Q =
    is-contr-is-equiv'
      ( fib (ev-Descent-data-circle l) Q)
      ( tot
        ( λ P →
          Eq-eq-Descent-data-circle Q (ev-Descent-data-circle l P) ∘
          inv))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ P →
          is-equiv-comp _ _
            ( is-equiv-inv _ _)
            ( is-equiv-Eq-eq-Descent-data-circle
              ( Q)
              ( ev-Descent-data-circle l P))))
      ( is-contr-map-is-equiv
        ( is-equiv-ev-Descent-data-circle-universal-property-circle
          ( l)
          ( up-circle))
        ( Q))
```

### Sections of type families over the circle are exactly the fixpoints of the automorphism from the characteristic descent data

```agda
module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : Descent-data-circle l2)
  ( αH : Eq-Descent-data-circle P (ev-Descent-data-circle l Q))
  where

  private
    α : type-Descent-data-circle P ≃ Q (base-free-loop l)
    α = pr1 αH

  map-path-over-loop-fib-aut-Descent-data-circle :
    ( x y : type-Descent-data-circle P) →
    ( map-equiv (aut-Descent-data-circle P) x ＝ y ) →
    ( path-over Q (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  map-path-over-loop-fib-aut-Descent-data-circle x y q =
    inv (pr2 αH _) ∙ (ap (map-equiv α) q)

  is-equiv-map-path-over-loop-fib-aut-Descent-data-circle :
    ( x y : type-Descent-data-circle P) →
    is-equiv (map-path-over-loop-fib-aut-Descent-data-circle x y)
  is-equiv-map-path-over-loop-fib-aut-Descent-data-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fib (map-equiv α) _)
        ( equiv-fib _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv α)
          ( _)))
      ( map-path-over-loop-fib-aut-Descent-data-circle x)
      ( _)

  equiv-path-over-loop-fib-aut-Descent-data-circle :
    ( x y : type-Descent-data-circle P) →
    ( map-equiv (aut-Descent-data-circle P) x ＝ y) ≃
    ( path-over Q (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  pr1 (equiv-path-over-loop-fib-aut-Descent-data-circle x y) =
    map-path-over-loop-fib-aut-Descent-data-circle x y
  pr2 (equiv-path-over-loop-fib-aut-Descent-data-circle x y) =
    is-equiv-map-path-over-loop-fib-aut-Descent-data-circle x y
```

```agda
module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : Descent-data-circle l2)
  ( αH : Eq-Descent-data-circle P (ev-Descent-data-circle l Q))
  where

  private
    α : type-Descent-data-circle P ≃ Q (base-free-loop l)
    α = pr1 αH

  ev-fixpoint-Descent-data-circle :
    ( (x : X) → Q x) → fixpoint-Descent-data-circle l P
  pr1 (ev-fixpoint-Descent-data-circle s) =
    map-inv-equiv
      ( α)
      ( s (base-free-loop l))
  pr2 (ev-fixpoint-Descent-data-circle s) =
    map-inv-is-equiv
      ( is-equiv-map-path-over-loop-fib-aut-Descent-data-circle l Q P αH _ _)
      ( ( ap (tr Q (loop-free-loop l)) (issec-map-inv-equiv α _)) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv (issec-map-inv-equiv α _))))

  equiv-fixpoint-Descent-data-circle-free-dependent-loop :
    fixpoint-Descent-data-circle l P ≃ free-dependent-loop l Q
  equiv-fixpoint-Descent-data-circle-free-dependent-loop =
    equiv-Σ
      ( _)
      ( α)
      ( λ x →
        equiv-path-over-loop-fib-aut-Descent-data-circle l Q P αH x x)

  comparison-fixpoint-Descent-data-circle :
    fixpoint-Descent-data-circle l P → free-dependent-loop l Q
  comparison-fixpoint-Descent-data-circle =
    map-equiv equiv-fixpoint-Descent-data-circle-free-dependent-loop

  triangle-comparison-fixpoint-Descent-data-circle :
    ( ev-free-loop-Π l Q) ~
    ( comparison-fixpoint-Descent-data-circle ∘
      ev-fixpoint-Descent-data-circle)
  triangle-comparison-fixpoint-Descent-data-circle s =
    eq-Eq-free-dependent-loop l Q
      ( ev-free-loop-Π l Q s)
      ( ( comparison-fixpoint-Descent-data-circle ∘
          ev-fixpoint-Descent-data-circle)
        ( s))
      ( inv issec-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl {x = ap _ (inv issec-inv-α)})
            ( issec-map-inv-is-equiv
              ( is-equiv-map-path-over-loop-fib-aut-Descent-data-circle l Q P αH _ _)
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

  is-equiv-comparison-fixpoint-Descent-data-circle :
    is-equiv comparison-fixpoint-Descent-data-circle
  is-equiv-comparison-fixpoint-Descent-data-circle =
    is-equiv-map-equiv equiv-fixpoint-Descent-data-circle-free-dependent-loop

  is-equiv-ev-fixpoint-Descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    is-equiv ev-fixpoint-Descent-data-circle
  is-equiv-ev-fixpoint-Descent-data-circle dup-circle =
    is-equiv-right-factor-htpy
      ( ev-free-loop-Π l Q)
      ( comparison-fixpoint-Descent-data-circle)
      ( ev-fixpoint-Descent-data-circle)
      ( triangle-comparison-fixpoint-Descent-data-circle)
      ( is-equiv-comparison-fixpoint-Descent-data-circle)
      ( dup-circle Q)

  equiv-ev-fixpoint-Descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    ( (x : X) → Q x) ≃ (fixpoint-Descent-data-circle l P)
  pr1 (equiv-ev-fixpoint-Descent-data-circle dup-circle) =
    ev-fixpoint-Descent-data-circle
  pr2 (equiv-ev-fixpoint-Descent-data-circle dup-circle) =
    is-equiv-ev-fixpoint-Descent-data-circle dup-circle

  compute-ev-fixpoint-Descent-data-circle :
    ( pr1 ∘ ev-fixpoint-Descent-data-circle ) ~
    ( (map-inv-equiv α) ∘ (ev-pt (base-free-loop l) _))
  compute-ev-fixpoint-Descent-data-circle = refl-htpy
```

### Families of maps over the circle are maps commuting with the respective automorphisms

```agda
module _
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  ( A : X → UU l2) (P : Descent-data-circle l2)
  ( αH : Eq-Descent-data-circle P (ev-Descent-data-circle l A))
  ( B : X → UU l3) (Q : Descent-data-circle l3)
  ( βK : Eq-Descent-data-circle Q (ev-Descent-data-circle l B))
  where

  private
    Y : UU l2
    Y = type-Descent-data-circle P
    e : Aut Y
    e = aut-Descent-data-circle P
    Z : UU l3
    Z = type-Descent-data-circle Q
    f : Aut Z
    f = aut-Descent-data-circle Q

    α : Y ≃ A (base-free-loop l)
    α = pr1 αH
    β : Z ≃ B (base-free-loop l)
    β = pr1 βK

  Descent-data-circle-function-type : Descent-data-circle (l2 ⊔ l3)
  pr1 Descent-data-circle-function-type =
    Y → Z
  pr2 Descent-data-circle-function-type =
    (equiv-postcomp _ f) ∘e (equiv-precomp (inv-equiv e) _)

  eq-Descent-data-circle-function-type :
    Eq-Descent-data-circle
      ( Descent-data-circle-function-type)
      ( ev-Descent-data-circle l (λ s → (A s → B s)))
  pr1 eq-Descent-data-circle-function-type =
    (equiv-postcomp _ β) ∘e (equiv-precomp (inv-equiv α) _)
  pr2 eq-Descent-data-circle-function-type h =
    ( eq-htpy
      ( htpy-comp-horizontal
        ( h ·l
          inv-htpy
            ( coherence-square-inv-all
              ( α)
              ( e)
              ( equiv-tr A (loop-free-loop l))
              ( α)
              ( pr2 αH)))
        ( pr2 βK))) ∙
    ( inv
      ( ( tr-function-type A B (loop-free-loop l))
        ( map-equiv (pr1 eq-Descent-data-circle-function-type) h)))

  equiv-fixpoint-Descent-data-circle-function-type-hom :
    fixpoint-Descent-data-circle l Descent-data-circle-function-type ≃
    hom-Descent-data-circle l P Q
  equiv-fixpoint-Descent-data-circle-function-type-hom =
    equiv-tot
      (λ h →
        ( equiv-inv-htpy _ _) ∘e
        ( ( inv-equiv (equiv-coherence-triangle-maps-inv-top _ _ e)) ∘e
          ( equiv-funext)))

  equiv-ev-Descent-data-circle-function-type-hom :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ((s : X) → A s → B s) ≃ (hom-Descent-data-circle l P Q)
  equiv-ev-Descent-data-circle-function-type-hom dup-circle =
    equiv-fixpoint-Descent-data-circle-function-type-hom ∘e
    ( equiv-ev-fixpoint-Descent-data-circle
      ( l)
      ( λ s → A s → B s)
      ( Descent-data-circle-function-type)
      ( eq-Descent-data-circle-function-type)
      ( dup-circle))
```
