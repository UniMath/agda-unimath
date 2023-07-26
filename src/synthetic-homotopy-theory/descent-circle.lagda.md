# The descent property of the circle

```agda
module synthetic-homotopy-theory.descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-types
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

By the universal property of the circle and univalence, a type family
`A : 𝕊¹ → U` is equivalent to a type `X : U` equipped with an automorphism
`e : X ≃ X`, in a way made precise in further sections of this file. The pair
`(X, e)` is called descent data for the circle.

```agda
descent-data-circle :
  ( l1 : Level) → UU (lsuc l1)
descent-data-circle l1 = Σ (UU l1) Aut

module _
  { l1 : Level} (P : descent-data-circle l1)
  where

  type-descent-data-circle : UU l1
  type-descent-data-circle = pr1 P

  aut-descent-data-circle : Aut type-descent-data-circle
  aut-descent-data-circle = pr2 P
```

### Dependent descent data for the circle

The equivalence extends to the dependent case, where given a type family `A`
over the circle with descent data `(X, e)`, a type family
`B : (t : 𝕊¹) → A t → U` is equivalent to a type family `R : X → U` equipped
with a family of equivalences `K : (x : X) → R(x) ≃ R(e(x))`. The pair `(R, K)`
is called dependent descent data for the circle. Intuitively, this states that
the types over points of `X` belonging to the same connected component in the
total space `Σ 𝕊¹ A` are equivalent.

```agda
dependent-descent-data-circle :
  { l1 : Level} → descent-data-circle l1 →
  ( l2 : Level) → UU (l1 ⊔ lsuc l2)
dependent-descent-data-circle P l2 =
  Σ ( type-descent-data-circle P → UU l2)
    ( λ R → equiv-fam R (R ∘ (map-equiv (aut-descent-data-circle P))))

module _
  { l1 l2 : Level} (P : descent-data-circle l1)
  ( Q : dependent-descent-data-circle P l2)
  where

  type-dependent-descent-data-circle : type-descent-data-circle P → UU l2
  type-dependent-descent-data-circle = pr1 Q

  equiv-dependent-descent-data-circle :
    equiv-fam
      type-dependent-descent-data-circle
      ( type-dependent-descent-data-circle ∘
        ( map-equiv (aut-descent-data-circle P)))
  equiv-dependent-descent-data-circle = pr2 Q
```

### Fixpoints of the descent data

A fixpoint of `(X, e)` is a fixpoint of `e`.

```agda
fixpoint-descent-data-circle :
  { l1 : Level}
  ( P : descent-data-circle l1) → UU l1
fixpoint-descent-data-circle P =
  Σ ( type-descent-data-circle P)
    ( λ p → (map-equiv (aut-descent-data-circle P) p) ＝ p)
```

### Homomorphisms between descent data for the circle

A homomorphism between `(X, e)` and `(Y, f)` is a map from `X` to `Y` such that
the obvious square commutes.

```agda
hom-descent-data-circle :
  { l1 l2 : Level}
  ( P : descent-data-circle l1) (Q : descent-data-circle l2) →
  UU (l1 ⊔ l2)
hom-descent-data-circle P Q =
  Σ ( (type-descent-data-circle P) → (type-descent-data-circle Q))
    ( λ h →
      coherence-square-maps
        ( h)
        ( map-equiv (aut-descent-data-circle P))
        ( map-equiv (aut-descent-data-circle Q))
        ( h))
```

### Canonical descent data for a family over the circle

A type family over the circle gives rise to its canonical descent data, obtained
by evaluation at `base` and transporting along `loop`.

```agda
ev-descent-data-circle :
  { l1 l2 : Level } {X : UU l1} (l : free-loop X) →
  (X → UU l2) → descent-data-circle l2
pr1 (ev-descent-data-circle l P) = P (base-free-loop l)
pr2 (ev-descent-data-circle l P) = equiv-tr P (loop-free-loop l)
```

## Properties

### Characterization of the identity type of descent data for the circle

```agda
Eq-descent-data-circle :
  { l1 : Level} → descent-data-circle l1 → descent-data-circle l1 →
  UU l1
Eq-descent-data-circle P Q =
  Σ ( (type-descent-data-circle P) ≃ (type-descent-data-circle Q))
    ( λ h →
      coherence-square-maps
        ( map-equiv h)
        ( map-equiv (aut-descent-data-circle P))
        ( map-equiv (aut-descent-data-circle Q))
        ( map-equiv h))

refl-Eq-descent-data-circle :
  { l1 : Level} (P : descent-data-circle l1) →
  Eq-descent-data-circle P P
refl-Eq-descent-data-circle P = id-equiv , refl-htpy

Eq-eq-descent-data-circle :
  { l1 : Level} (P Q : descent-data-circle l1) →
  P ＝ Q → Eq-descent-data-circle P Q
Eq-eq-descent-data-circle P .P refl = refl-Eq-descent-data-circle P

is-contr-total-Eq-descent-data-circle :
  { l1 : Level} (P : descent-data-circle l1) →
  is-contr (Σ (descent-data-circle l1) (Eq-descent-data-circle P))
is-contr-total-Eq-descent-data-circle P =
  is-contr-total-Eq-structure
    ( λ Y f h →
      coherence-square-maps
        ( map-equiv h)
        ( map-equiv (aut-descent-data-circle P))
        ( map-equiv f)
        ( map-equiv h))
    ( is-contr-total-equiv (type-descent-data-circle P))
    ( type-descent-data-circle P , id-equiv)
  ( is-contr-total-htpy-equiv (aut-descent-data-circle P))

is-equiv-Eq-eq-descent-data-circle :
  { l1 : Level} (P Q : descent-data-circle l1) →
  is-equiv (Eq-eq-descent-data-circle P Q)
is-equiv-Eq-eq-descent-data-circle P =
  fundamental-theorem-id
    ( is-contr-total-Eq-descent-data-circle P)
    ( Eq-eq-descent-data-circle P)

eq-Eq-descent-data-circle :
  { l1 : Level} (P Q : descent-data-circle l1) →
  Eq-descent-data-circle P Q → P ＝ Q
eq-Eq-descent-data-circle P Q =
  map-inv-is-equiv (is-equiv-Eq-eq-descent-data-circle P Q)
```

### Uniqueness of descent data characterizing a particular type family over the circle

```agda
comparison-descent-data-circle :
  ( l1 : Level) → free-loop (UU l1) → descent-data-circle l1
comparison-descent-data-circle l1 = tot (λ Y → equiv-eq)

is-equiv-comparison-descent-data-circle :
  ( l1 : Level) → is-equiv (comparison-descent-data-circle l1)
is-equiv-comparison-descent-data-circle l1 =
  is-equiv-tot-is-fiberwise-equiv (λ Y → univalence Y Y)

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  where

  triangle-comparison-descent-data-circle :
    coherence-triangle-maps
      ( ev-descent-data-circle l)
      ( comparison-descent-data-circle l2)
      ( ev-free-loop l (UU l2))
  triangle-comparison-descent-data-circle P =
    eq-Eq-descent-data-circle
      ( ev-descent-data-circle l P)
      ( comparison-descent-data-circle l2 (ev-free-loop l (UU l2) P))
      ( id-equiv , (htpy-eq (inv (compute-equiv-eq-ap (loop-free-loop l)))))

  is-equiv-ev-descent-data-circle-universal-property-circle :
    ( up-circle : universal-property-circle (lsuc l2) l) →
    is-equiv (ev-descent-data-circle l)
  is-equiv-ev-descent-data-circle-universal-property-circle up-circle =
    is-equiv-comp-htpy
      ( ev-descent-data-circle l)
      ( comparison-descent-data-circle l2)
      ( ev-free-loop l (UU l2))
      ( triangle-comparison-descent-data-circle)
      ( up-circle (UU l2))
      ( is-equiv-comparison-descent-data-circle l2)

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loop X) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {X} l =
  ( Q : descent-data-circle l2) →
    is-contr
    ( Σ (X → UU l2)
        (λ P → Eq-descent-data-circle Q (ev-descent-data-circle l P)))

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  where

  unique-family-property-universal-property-circle :
    universal-property-circle (lsuc l2) l →
    unique-family-property-circle l2 l
  unique-family-property-universal-property-circle up-circle Q =
    is-contr-is-equiv'
      ( fib (ev-descent-data-circle l) Q)
      ( tot
        ( λ P →
          Eq-eq-descent-data-circle Q (ev-descent-data-circle l P) ∘
          inv))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ P →
          is-equiv-comp _ _
            ( is-equiv-inv _ _)
            ( is-equiv-Eq-eq-descent-data-circle
              ( Q)
              ( ev-descent-data-circle l P))))
      ( is-contr-map-is-equiv
        ( is-equiv-ev-descent-data-circle-universal-property-circle
          ( l)
          ( up-circle))
        ( Q))
```

### Characterization of sections of type families over the circle

Sections of type families over the circle are exactly the fixpoints of the
automorphism from the characteristic descent data.

```agda
module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P (ev-descent-data-circle l Q))
  where

  private
    α : type-descent-data-circle P ≃ Q (base-free-loop l)
    α = pr1 αH

  map-compute-dependent-identification-loop-circle :
    ( x y : type-descent-data-circle P) →
    map-equiv (aut-descent-data-circle P) x ＝ y →
    dependent-identification Q
      ( loop-free-loop l)
      ( map-equiv α x)
      ( map-equiv α y)
  map-compute-dependent-identification-loop-circle x y q =
    inv (pr2 αH x) ∙ (ap (map-equiv α) q)

  is-equiv-map-compute-dependent-identification-loop-circle :
    ( x y : type-descent-data-circle P) →
    is-equiv (map-compute-dependent-identification-loop-circle x y)
  is-equiv-map-compute-dependent-identification-loop-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fib (map-equiv α) (tr Q (loop-free-loop l) (map-equiv α x)))
        ( equiv-fib _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv α)
          ( tr Q (loop-free-loop l) (map-equiv α x))))
      ( map-compute-dependent-identification-loop-circle x)
      ( y)

  compute-dependent-identification-loop-circle :
    ( x y : type-descent-data-circle P) →
    ( map-equiv (aut-descent-data-circle P) x ＝ y) ≃
    ( dependent-identification Q
      ( loop-free-loop l)
      ( map-equiv α x)
      ( map-equiv α y))
  pr1 (compute-dependent-identification-loop-circle x y) =
    map-compute-dependent-identification-loop-circle x y
  pr2 (compute-dependent-identification-loop-circle x y) =
    is-equiv-map-compute-dependent-identification-loop-circle x y
```

```agda
module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P (ev-descent-data-circle l Q))
  where

  private
    α : type-descent-data-circle P ≃ Q (base-free-loop l)
    α = pr1 αH

  ev-fixpoint-descent-data-circle :
    ( (x : X) → Q x) → fixpoint-descent-data-circle P
  pr1 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( α)
      ( s (base-free-loop l))
  pr2 (ev-fixpoint-descent-data-circle s) =
    map-inv-is-equiv
      ( is-equiv-map-compute-dependent-identification-loop-circle
        ( l)
        ( Q)
        ( P)
        ( αH)
        ( map-inv-equiv α (s (base-free-loop l)))
        ( map-inv-equiv α (s (base-free-loop l))))
      ( ( ap
          ( tr Q (loop-free-loop l))
          ( is-section-map-inv-equiv α (s (base-free-loop l)))) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv (is-section-map-inv-equiv α (s (base-free-loop l))))))

  equiv-fixpoint-descent-data-circle-free-dependent-loop :
    fixpoint-descent-data-circle P ≃ free-dependent-loop l Q
  equiv-fixpoint-descent-data-circle-free-dependent-loop =
    equiv-Σ
      ( λ x → dependent-identification Q (loop-free-loop l) x x)
      ( α)
      ( λ x →
        compute-dependent-identification-loop-circle l Q P αH x x)

  comparison-fixpoint-descent-data-circle :
    fixpoint-descent-data-circle P → free-dependent-loop l Q
  comparison-fixpoint-descent-data-circle =
    map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  triangle-comparison-fixpoint-descent-data-circle :
    coherence-triangle-maps
      ( ev-free-loop-Π l Q)
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
  triangle-comparison-fixpoint-descent-data-circle s =
    eq-Eq-free-dependent-loop l Q
      ( ev-free-loop-Π l Q s)
      ( ( comparison-fixpoint-descent-data-circle ∘
          ev-fixpoint-descent-data-circle)
        ( s))
      ( inv is-section-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl {x = ap (tr Q (loop-free-loop l)) (inv is-section-inv-α)})
            ( is-section-map-inv-is-equiv
              ( is-equiv-map-compute-dependent-identification-loop-circle
                ( l)
                ( Q)
                ( P)
                ( αH)
                ( map-inv-equiv α (s (base-free-loop l)))
                ( pr1 (ev-fixpoint-descent-data-circle s)))
              ( _))) ∙
          ( ( inv (assoc (ap _ (inv is-section-inv-α)) _ _)) ∙
            ( horizontal-concat-Id²
              ( inv
                ( ap-concat-eq (tr Q (loop-free-loop l))
                  ( inv is-section-inv-α)
                  ( is-section-inv-α)
                  ( refl)
                  ( inv (left-inv is-section-inv-α))))
              ( refl)))))
    where
    is-section-inv-α :
      eq-value (map-equiv α ∘ map-inv-equiv α) id (s (base-free-loop l))
    is-section-inv-α = is-section-map-inv-equiv α (s (base-free-loop l))

  is-equiv-comparison-fixpoint-descent-data-circle :
    is-equiv comparison-fixpoint-descent-data-circle
  is-equiv-comparison-fixpoint-descent-data-circle =
    is-equiv-map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  is-equiv-ev-fixpoint-descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    is-equiv ev-fixpoint-descent-data-circle
  is-equiv-ev-fixpoint-descent-data-circle dup-circle =
    is-equiv-right-factor-htpy
      ( ev-free-loop-Π l Q)
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
      ( triangle-comparison-fixpoint-descent-data-circle)
      ( is-equiv-comparison-fixpoint-descent-data-circle)
      ( dup-circle Q)

  equiv-ev-fixpoint-descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    ( (x : X) → Q x) ≃ (fixpoint-descent-data-circle P)
  pr1 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    ev-fixpoint-descent-data-circle
  pr2 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    is-equiv-ev-fixpoint-descent-data-circle dup-circle

  compute-ev-fixpoint-descent-data-circle :
    coherence-square-maps
      ( ev-fixpoint-descent-data-circle)
      ( ev-point (base-free-loop l) {Q})
      ( pr1)
      ( map-inv-equiv α)
  compute-ev-fixpoint-descent-data-circle = refl-htpy
```

### Characterization of families of maps over the circle

Families of maps over the circle are maps commuting with the respective
automorphisms.

```agda
module _
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  ( A : X → UU l2) (P : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P (ev-descent-data-circle l A))
  ( B : X → UU l3) (Q : descent-data-circle l3)
  ( βK : Eq-descent-data-circle Q (ev-descent-data-circle l B))
  where

  private
    Y : UU l2
    Y = type-descent-data-circle P
    e : Aut Y
    e = aut-descent-data-circle P
    Z : UU l3
    Z = type-descent-data-circle Q
    f : Aut Z
    f = aut-descent-data-circle Q

    α : Y ≃ A (base-free-loop l)
    α = pr1 αH
    β : Z ≃ B (base-free-loop l)
    β = pr1 βK

  descent-data-circle-function-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-function-type =
    Y → Z
  pr2 descent-data-circle-function-type =
    (equiv-postcomp Y f) ∘e (equiv-precomp (inv-equiv e) Z)

  eq-descent-data-circle-function-type :
    Eq-descent-data-circle
      ( descent-data-circle-function-type)
      ( ev-descent-data-circle l (λ s → (A s → B s)))
  pr1 eq-descent-data-circle-function-type =
    (equiv-postcomp (A (base-free-loop l)) β) ∘e (equiv-precomp (inv-equiv α) Z)
  pr2 eq-descent-data-circle-function-type h =
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
        ( map-equiv (pr1 eq-descent-data-circle-function-type) h)))

  equiv-fixpoint-descent-data-circle-function-type-hom :
    fixpoint-descent-data-circle descent-data-circle-function-type ≃
    hom-descent-data-circle P Q
  equiv-fixpoint-descent-data-circle-function-type-hom =
    equiv-tot
      (λ h →
        ( equiv-inv-htpy (((map-equiv f) ∘ h)) (h ∘ (map-equiv e))) ∘e
        ( ( inv-equiv
            ( equiv-coherence-triangle-maps-inv-top ((map-equiv f) ∘ h) h e)) ∘e
          ( equiv-funext)))

  equiv-ev-descent-data-circle-function-type-hom :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ((s : X) → A s → B s) ≃ (hom-descent-data-circle P Q)
  equiv-ev-descent-data-circle-function-type-hom dup-circle =
    equiv-fixpoint-descent-data-circle-function-type-hom ∘e
    ( equiv-ev-fixpoint-descent-data-circle
      ( l)
      ( λ s → A s → B s)
      ( descent-data-circle-function-type)
      ( eq-descent-data-circle-function-type)
      ( dup-circle))
```
