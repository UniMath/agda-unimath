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
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-dependent-function-types
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

```agda
descent-data-circle-Π :
  { l1 : Level} → descent-data-circle l1 →
  ( l2 : Level) → UU (l1 ⊔ lsuc l2)
descent-data-circle-Π P l2 =
  Σ ( type-descent-data-circle P → UU l2)
    ( λ R → equiv-fam R (R ∘ (map-equiv (aut-descent-data-circle P))))

module _
  { l1 l2 : Level} (P : descent-data-circle l1)
  ( Q : descent-data-circle-Π P l2)
  where

  type-descent-data-circle-Π : type-descent-data-circle P → UU l2
  type-descent-data-circle-Π = pr1 Q

  equiv-descent-data-circle-Π :
    equiv-fam
      type-descent-data-circle-Π
      (type-descent-data-circle-Π ∘ (map-equiv (aut-descent-data-circle P)))
  equiv-descent-data-circle-Π = pr2 Q
```

### Fixpoints of the descent data

```agda
fixpoint-descent-data-circle :
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( P : descent-data-circle l2) → UU l2
fixpoint-descent-data-circle l P =
  Σ ( type-descent-data-circle P)
    ( λ p → (map-equiv (aut-descent-data-circle P) p) ＝ p)
```

### Homomorphisms between descent data for the circle

```agda
hom-descent-data-circle :
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  ( P : descent-data-circle l2) (Q : descent-data-circle l3) →
  UU (l2 ⊔ l3)
hom-descent-data-circle _ P Q =
  Σ ( (type-descent-data-circle P) → (type-descent-data-circle Q))
    ( λ h →
      coherence-square-maps
        ( h)
        ( map-equiv (aut-descent-data-circle P))
        ( map-equiv (aut-descent-data-circle Q))
        ( h))
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

### Characterization of the identity type of dependent descent data for the circle

```agda
module _
  { l1 l2 : Level} (P : descent-data-circle l1)
  where

  Eq-descent-data-circle-Π :
    descent-data-circle-Π P l2 → descent-data-circle-Π P l2
    → UU (l1 ⊔ l2)
  Eq-descent-data-circle-Π A B =
    Σ ( equiv-fam (type-descent-data-circle-Π P A) (type-descent-data-circle-Π P B))
      ( λ H → ( x : type-descent-data-circle P) →
              coherence-square-maps
                ( map-equiv (H x))
                ( map-equiv (equiv-descent-data-circle-Π P A x))
                ( map-equiv (equiv-descent-data-circle-Π P B x))
                ( map-equiv (H (map-equiv (aut-descent-data-circle P) x))))

  refl-Eq-descent-data-circle-Π :
    ( A : descent-data-circle-Π P l2) →
    Eq-descent-data-circle-Π A A
  pr1 (refl-Eq-descent-data-circle-Π A) = id-equiv-fam (type-descent-data-circle-Π P A)
  pr2 (refl-Eq-descent-data-circle-Π A) x = refl-htpy

  Eq-eq-descent-data-circle-Π :
    ( A B : descent-data-circle-Π P l2) →
    A ＝ B → Eq-descent-data-circle-Π A B
  Eq-eq-descent-data-circle-Π A .A refl = refl-Eq-descent-data-circle-Π A

  is-contr-total-Eq-descent-data-circle-Π :
    ( A : descent-data-circle-Π P l2) →
    is-contr (Σ (descent-data-circle-Π P l2) (Eq-descent-data-circle-Π A))
  is-contr-total-Eq-descent-data-circle-Π A =
    is-contr-total-Eq-structure
      ( λ R K H →
        (x : type-descent-data-circle P) →
          coherence-square-maps
            ( map-equiv (H x))
            ( map-equiv (equiv-descent-data-circle-Π P A x))
            ( map-equiv (K x))
            ( map-equiv (H (map-equiv (aut-descent-data-circle P) x))))
      ( is-contr-total-equiv-fam (type-descent-data-circle-Π P A))
      ( type-descent-data-circle-Π P A , (id-equiv-fam (type-descent-data-circle-Π P A)))
      ( is-contr-total-Eq-Π
        ( λ x K → (map-equiv (equiv-descent-data-circle-Π P A x)) ~ (map-equiv K))
        ( λ x → is-contr-total-htpy-equiv (equiv-descent-data-circle-Π P A x)))

  is-equiv-Eq-eq-descent-data-circle-Π :
    ( A B : descent-data-circle-Π P l2) →
    is-equiv (Eq-eq-descent-data-circle-Π A B)
  is-equiv-Eq-eq-descent-data-circle-Π A =
    fundamental-theorem-id
      ( is-contr-total-Eq-descent-data-circle-Π A)
      ( Eq-eq-descent-data-circle-Π A)

  eq-Eq-descent-data-circle-Π :
    ( A B : descent-data-circle-Π P l2) →
    Eq-descent-data-circle-Π A B → A ＝ B
  eq-Eq-descent-data-circle-Π A B =
    map-inv-is-equiv (is-equiv-Eq-eq-descent-data-circle-Π A B)
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

  ev-descent-data-circle : (X → UU l2) → descent-data-circle l2
  pr1 (ev-descent-data-circle P) = P (base-free-loop l)
  pr2 (ev-descent-data-circle P) = equiv-tr P (loop-free-loop l)

  triangle-comparison-descent-data-circle :
    coherence-triangle-maps
      ( ev-descent-data-circle)
      ( comparison-descent-data-circle l2)
      ( ev-free-loop l (UU l2))
  triangle-comparison-descent-data-circle P =
    eq-Eq-descent-data-circle
      ( ev-descent-data-circle P)
      ( comparison-descent-data-circle l2 (ev-free-loop l (UU l2) P))
      ( id-equiv , (htpy-eq (inv (compute-equiv-eq-ap (loop-free-loop l)))))

  is-equiv-ev-descent-data-circle-universal-property-circle :
    ( up-circle : universal-property-circle (lsuc l2) l) →
    is-equiv ev-descent-data-circle
  is-equiv-ev-descent-data-circle-universal-property-circle up-circle =
    is-equiv-comp-htpy
      ( ev-descent-data-circle)
      ( comparison-descent-data-circle l2)
      ( ev-free-loop l (UU l2))
      ( triangle-comparison-descent-data-circle)
      ( up-circle (UU l2))
      ( is-equiv-comparison-descent-data-circle l2)

  family-descent-data-circle : descent-data-circle l2 → UU (l1 ⊔ lsuc l2)
  family-descent-data-circle Q =
    Σ ( X → UU l2)
      ( λ P → Eq-descent-data-circle Q (ev-descent-data-circle P))

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {X : UU l1} (l : free-loop X) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {X} l =
  ( Q : descent-data-circle l2) → is-contr (family-descent-data-circle l Q)

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

### Uniqueness of dependent descent data characterizing a type family over a family over the circle

```agda
module _
  { l1 l2 l3 : Level} {X : UU l1} (l : free-loop X)
  ( Q : X → UU l2) (P : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P (ev-descent-data-circle l Q))
  where

  private
    α : type-descent-data-circle P ≃ Q (base-free-loop l)
    α = pr1 αH
    e : Aut (type-descent-data-circle P)
    e = aut-descent-data-circle P

  comparison-descent-data-circle-Π :
    free-dependent-loop l (λ t → (Q t → UU l3)) ≃
    descent-data-circle-Π P l3
  comparison-descent-data-circle-Π =
    equiv-Σ
      ( λ R → equiv-fam R (R ∘ (map-equiv e)))
      ( equiv-precomp α (UU l3))
      ( λ R →
          equivalence-reasoning
            ( (tr (λ t → Q t → UU l3) (loop-free-loop l) R ＝ R))
            ≃ ( (tr (λ _ → UU l3) (loop-free-loop l) ∘ R) ~
                (R ∘ (tr Q (loop-free-loop l))))
              by inv-equiv
                  ( compute-path-over-function-type
                      ( Q)
                      ( λ _ → UU l3)
                      ( loop-free-loop l)
                      ( R)
                      ( R))
            ≃ (R ~ (R ∘ (tr Q (loop-free-loop l))))
              by equiv-concat-htpy
                  ( (inv-htpy (tr-const (loop-free-loop l))) ·r R)
                  ( (R ∘ (tr Q (loop-free-loop l))))
            ≃ equiv-fam
                ( R ∘ map-equiv α)
                ( R ∘ (map-equiv α ∘ (map-equiv e)))
              by inv-equiv
                  ( equiv-Π
                    ( eq-value R (R ∘ tr Q (loop-free-loop l)))
                    ( pr1 αH)
                    ( λ a' →
                      ( equiv-concat'
                        ( R (map-equiv α a'))
                        ( ap R (pr2 αH a'))) ∘e
                      ( inv-equiv equiv-univalence))))

  ev-descent-data-circle-Π :
    ((x : X) → (Q x) → UU l3) → descent-data-circle-Π P l3
  pr1 (ev-descent-data-circle-Π A) =
    A (base-free-loop l) ∘ map-equiv (pr1 αH)
  pr2 (ev-descent-data-circle-Π A) x =
    equiv-tr (ind-Σ A) (eq-pair-Σ (loop-free-loop l) (inv (pr2 αH x)))

  triangle-comparison-descent-data-circle-Π :
    coherence-triangle-maps
      ( ev-descent-data-circle-Π)
      ( map-equiv comparison-descent-data-circle-Π)
      ( ev-free-loop-Π l (λ t → Q t → UU l3))
  triangle-comparison-descent-data-circle-Π A =
    eq-Eq-descent-data-circle-Π P
      ( ev-descent-data-circle-Π A)
      ( map-equiv comparison-descent-data-circle-Π
        ( ev-free-loop-Π l (λ t → Q t → UU l3) A))
      ( id-equiv-fam _ ,
        λ x a →
          equational-reasoning
            tr (ind-Σ A) (eq-pair-Σ (loop-free-loop l) (inv (pr2 αH x))) a
            ＝ {!!}
              by {!!}
            ＝ map-equiv
                 (map-inv-equiv
                   (equiv-Π
                    (λ x → Id (A (pr1 l) x) (A (pr1 l) (tr Q (pr2 l) x))) (pr1 αH)
                    (λ a' →
                       equiv-comp
                       (equiv-concat' (A (pr1 l) (pr1 (pr1 αH) a'))
                        (ap (A (pr1 l)) (pr2 αH a')))
                       (inv-equiv equiv-univalence)))
                    (λ y →
                      ( inv (tr-const (pr2 l) (A (pr1 l) y))) ∙
                      ( map-inv-equiv
                        ( compute-path-over-function-type Q (λ _ → UU l3) (pr2 l)
                            ( A (pr1 l)) (A (pr1 l)))
                        ( apd A (pr2 l)))
                        ( y))
                  x)
                 a
              by {!!}
            ＝ map-equiv
                 (map-inv-equiv
                   (equiv-Π
                    (λ x → Id (A (pr1 l) x) (A (pr1 l) (tr Q (pr2 l) x))) (pr1 αH)
                    (λ a' →
                       equiv-comp
                       (equiv-concat' (A (pr1 l) (pr1 (pr1 αH) a'))
                        (ap (A (pr1 l)) (pr2 αH a')))
                       (inv-equiv equiv-univalence)))
                    (λ y →
                      ( inv (tr-const (pr2 l) (A (pr1 l) y))) ∙
                      ( map-inv-equiv
                        ( compute-path-over-function-type Q (λ _ → UU l3) (pr2 l)
                            ( A (pr1 l)) (A (pr1 l)))
                        ( apd A (pr2 l)))
                        ( y))
                  x)
                 a
              by {!!})

  is-equiv-ev-descent-data-circle-Π-universal-property-circle :
    ( dup-circle : dependent-universal-property-circle (l2 ⊔ lsuc l3) l) →
    is-equiv ev-descent-data-circle-Π
  is-equiv-ev-descent-data-circle-Π-universal-property-circle dup-circle =
    is-equiv-comp-htpy
      ( ev-descent-data-circle-Π)
      ( map-equiv comparison-descent-data-circle-Π)
      ( ev-free-loop-Π l (λ t → Q t → UU l3))
      ( triangle-comparison-descent-data-circle-Π)
      ( dup-circle (λ t → Q t → UU l3))
      ( is-equiv-map-equiv comparison-descent-data-circle-Π)

  family-descent-data-circle-Π :
    descent-data-circle-Π P l3 → UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-descent-data-circle-Π A =
    Σ ( (x : X) → Q x → UU l3)
      ( λ R → Eq-descent-data-circle-Π P A (ev-descent-data-circle-Π R) )

  unique-family-property-circle-Π : UU (l1 ⊔ l2 ⊔ lsuc l3)
  unique-family-property-circle-Π =
    (A : descent-data-circle-Π P l3) → is-contr (family-descent-data-circle-Π A)

  unique-family-property-dependent-universal-property-circle-Π :
    dependent-universal-property-circle (l2 ⊔ lsuc l3) l →
    unique-family-property-circle-Π
  unique-family-property-dependent-universal-property-circle-Π dup-circle A =
    is-contr-is-equiv'
      ( fib ev-descent-data-circle-Π A)
      ( tot
        ( λ B →
          Eq-eq-descent-data-circle-Π P A (ev-descent-data-circle-Π B) ∘
          inv))
      ( is-equiv-tot-is-fiberwise-equiv
        ( λ B →
          is-equiv-comp _ _
            ( is-equiv-inv _ _)
            ( is-equiv-Eq-eq-descent-data-circle-Π P
              ( A)
              ( ev-descent-data-circle-Π B))))
      ( is-contr-map-is-equiv
        ( is-equiv-ev-descent-data-circle-Π-universal-property-circle dup-circle)
        ( A))
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

  map-compute-path-over-loop-circle :
    ( x y : type-descent-data-circle P) →
    ( map-equiv (aut-descent-data-circle P) x ＝ y) →
    ( path-over Q (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  map-compute-path-over-loop-circle x y q =
    inv (pr2 αH x) ∙ (ap (map-equiv α) q)

  is-equiv-map-compute-path-over-loop-circle :
    ( x y : type-descent-data-circle P) →
    is-equiv (map-compute-path-over-loop-circle x y)
  is-equiv-map-compute-path-over-loop-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fib (map-equiv α) (tr Q (loop-free-loop l) (map-equiv α x)))
        ( equiv-fib _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv α)
          ( tr Q (loop-free-loop l) (map-equiv α x))))
      ( map-compute-path-over-loop-circle x)
      ( y)

  compute-path-over-loop-circle :
    ( x y : type-descent-data-circle P) →
    ( map-equiv (aut-descent-data-circle P) x ＝ y) ≃
    ( path-over Q (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  pr1 (compute-path-over-loop-circle x y) =
    map-compute-path-over-loop-circle x y
  pr2 (compute-path-over-loop-circle x y) =
    is-equiv-map-compute-path-over-loop-circle x y
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
    ( (x : X) → Q x) → fixpoint-descent-data-circle l P
  pr1 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( α)
      ( s (base-free-loop l))
  pr2 (ev-fixpoint-descent-data-circle s) =
    map-inv-is-equiv
      ( is-equiv-map-compute-path-over-loop-circle
        ( l)
        ( Q)
        ( P)
        ( αH)
        ( map-inv-equiv α (s (base-free-loop l)))
        ( map-inv-equiv α (s (base-free-loop l))))
      ( ( ap
          ( tr Q (loop-free-loop l))
          ( issec-map-inv-equiv α (s (base-free-loop l)))) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv (issec-map-inv-equiv α (s (base-free-loop l))))))

  equiv-fixpoint-descent-data-circle-free-dependent-loop :
    fixpoint-descent-data-circle l P ≃ free-dependent-loop l Q
  equiv-fixpoint-descent-data-circle-free-dependent-loop =
    equiv-Σ
      ( λ x → path-over Q (loop-free-loop l) x x)
      ( α)
      ( λ x →
        compute-path-over-loop-circle l Q P αH x x)

  comparison-fixpoint-descent-data-circle :
    fixpoint-descent-data-circle l P → free-dependent-loop l Q
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
      ( inv issec-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl {x = ap (tr Q (loop-free-loop l)) (inv issec-inv-α)})
            ( issec-map-inv-is-equiv
              ( is-equiv-map-compute-path-over-loop-circle
                ( l)
                ( Q)
                ( P)
                ( αH)
                ( map-inv-equiv α (s (base-free-loop l)))
                ( pr1 (ev-fixpoint-descent-data-circle s)))
              ( _))) ∙
          ( ( inv (assoc (ap _ (inv issec-inv-α)) _ _)) ∙
            ( horizontal-concat-Id²
              ( inv
                ( ap-concat-eq (tr Q (loop-free-loop l))
                  ( inv issec-inv-α)
                  ( issec-inv-α)
                  ( refl)
                  ( inv (left-inv issec-inv-α))))
              ( refl)))))
    where
    issec-inv-α :
      eq-value (map-equiv α ∘ map-inv-equiv α) id (s (base-free-loop l))
    issec-inv-α = issec-map-inv-equiv α (s (base-free-loop l))

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
    ( (x : X) → Q x) ≃ (fixpoint-descent-data-circle l P)
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
    fixpoint-descent-data-circle l descent-data-circle-function-type ≃
    hom-descent-data-circle l P Q
  equiv-fixpoint-descent-data-circle-function-type-hom =
    equiv-tot
      (λ h →
        ( equiv-inv-htpy (((map-equiv f) ∘ h)) (h ∘ (map-equiv e))) ∘e
        ( ( inv-equiv
            ( equiv-coherence-triangle-maps-inv-top ((map-equiv f) ∘ h) h e)) ∘e
          ( equiv-funext)))

  equiv-ev-descent-data-circle-function-type-hom :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ((s : X) → A s → B s) ≃ (hom-descent-data-circle l P Q)
  equiv-ev-descent-data-circle-function-type-hom dup-circle =
    equiv-fixpoint-descent-data-circle-function-type-hom ∘e
    ( equiv-ev-fixpoint-descent-data-circle
      ( l)
      ( λ s → A s → B s)
      ( descent-data-circle-function-type)
      ( eq-descent-data-circle-function-type)
      ( dup-circle))
```

### Characterization of descent data for constant families over the circle

```agda
module _
  { l1 l2 : Level } {X : UU l1} (l : free-loop X)
  ( A : UU l2)
  where

  descent-data-circle-constant-type : descent-data-circle l2
  pr1 descent-data-circle-constant-type = A
  pr2 descent-data-circle-constant-type = id-equiv

  eq-descent-data-circle-constant-type :
    Eq-descent-data-circle
      ( descent-data-circle-constant-type)
      ( ev-descent-data-circle l (λ x → A))
  pr1 eq-descent-data-circle-constant-type = id-equiv
  pr2 eq-descent-data-circle-constant-type = inv-htpy (tr-const (loop-free-loop l))
```

### Characterization of descent data for dependent pair types indexed by a type family over the circle

```agda
module _
  { l1 l2 l3 l4 : Level} {X : UU l1} (l : free-loop X)
  ( A : X → UU l2) (P : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P (ev-descent-data-circle l A))
  ( B : (x : X) → (A x) → UU l4)
  ( Q : descent-data-circle-Π P l4)
  ( βK : Eq-descent-data-circle-Π P Q (ev-descent-data-circle-Π l A P αH B))
  where

  private
    Y : UU l2
    Y = type-descent-data-circle P
    e : Y ≃ Y
    e = aut-descent-data-circle P
    α : Y ≃ A (base-free-loop l)
    α = pr1 αH

    Z : Y → UU l4
    Z = type-descent-data-circle-Π P Q
    β : (x : Y) → (Z x) ≃ (B (base-free-loop l) (map-equiv α x))
    β = pr1 βK
    β' : (x : Y) → (Z x) → (B (base-free-loop l) (map-equiv α x))
    β' x = map-equiv (β x)
    f : (x : Y) → (Z x) ≃ (Z (map-equiv e x))
    f = equiv-descent-data-circle-Π P Q


  descent-data-circle-dependent-pair-type : descent-data-circle (l2 ⊔ l4)
  pr1 descent-data-circle-dependent-pair-type = Σ Y Z
  pr2 descent-data-circle-dependent-pair-type = equiv-Σ Z e f

  eq-descent-data-circle-dependent-pair-type :
    Eq-descent-data-circle
      ( descent-data-circle-dependent-pair-type)
      ( ev-descent-data-circle l (λ t → Σ (A t) (B t)))
  pr1 eq-descent-data-circle-dependent-pair-type =
    equiv-Σ (B (base-free-loop l)) α β
  pr2 eq-descent-data-circle-dependent-pair-type u =
    inv
      ( equational-reasoning
        tr (λ t → Σ (A t) (B t)) (loop-free-loop l) v
        ＝ ( tr A (loop-free-loop l) (pr1 v)) ,
              tr (ind-Σ B) (eq-pair-Σ (loop-free-loop l) refl) (pr2 v)
          by tr-Σ B (loop-free-loop l) (map-Σ _ (map-equiv α) β' u)
        ＝ ( map-equiv α (map-equiv e (pr1 u))) ,
              map-equiv (β (map-equiv e (pr1 u))) (pr1 (pr2 Q (pr1 u)) (pr2 u))
          by
            eq-pair-Σ
              ( inv (pr2 αH (pr1 u)))
              ( inv
                ( ( pr2 βK (pr1 u) (pr2 u)) ∙
                  ( tr-eq-pair-Σ
                    ( ind-Σ B)
                    ( loop-free-loop l)
                    ( inv (pr2 αH (pr1 u))) (pr2 v)))))
    where
    v : Σ (A (base-free-loop l)) (B (base-free-loop l))
    v = map-Σ (B (base-free-loop l)) (map-equiv α) β' u
```

### Characterization of equivalences between families over the circle

```agda

baz : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
      (f : B → C) (g : C → D) (h : A → D) (e : B ≃ A) →
      ((g ∘ (f ∘ (map-inv-equiv e))) ~ h) ≃ ((g ∘ f) ~ (h ∘ (map-equiv e)))
baz f g h e =
  equivalence-reasoning
    ((g ∘ (f ∘ map-inv-equiv e)) ~ h)
    ≃ ((g ∘ (f ∘ (map-inv-equiv e ∘ (map-equiv e)))) ~ (h ∘ (map-equiv e)))
      by {!!}
    ≃ ((g ∘ f) ~ (h ∘ map-equiv e))
      by equiv-concat-htpy ((g ∘ f) ·l (inv-htpy (isretr-map-inv-equiv e))) (h ∘ map-equiv e)

module _
  { l1 l2 : Level} {X : UU l1} (l : free-loop X)
  ( A : X → UU l2) (P : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P (ev-descent-data-circle l A))
  ( B : X → UU l2) (Q : descent-data-circle l2)
  ( βK : Eq-descent-data-circle Q (ev-descent-data-circle l B))
  where

  private
    Y : UU l2
    Y = type-descent-data-circle P
    e : Y ≃ Y
    e = aut-descent-data-circle P
    Z : UU l2
    Z = type-descent-data-circle Q
    f : Z ≃ Z
    f = aut-descent-data-circle Q

  bar : descent-data-circle-Π (descent-data-circle-function-type l A P αH B Q βK) _
  pr1 bar f = is-equiv f
  pr2 bar f = {!equiv-comp!}

  foo : ({k : Level} → dependent-universal-property-circle k l) →
        equiv-fam A B ≃
        ( Σ ( Y ≃ Z)
            ( λ h →
              coherence-square-maps
                (map-equiv h)
                (map-equiv e)
                (map-equiv f)
                (map-equiv h)))
  foo dup-circle = equivalence-reasoning
        ((t : X) → (A t) ≃ (B t))
        ≃ fixpoint-descent-data-circle
          ( l)
          ( [i])
          by equiv-ev-fixpoint-descent-data-circle l (λ t → A t ≃ B t) [i] [ii] dup-circle
        ≃ Σ (Y ≃ Z) (λ h → (map-equiv f ∘ (map-equiv h ∘ (map-inv-equiv e))) ~ (map-equiv h))
          by equiv-tot (λ x → extensionality-equiv _ _)
        ≃ Σ (Y ≃ Z) (λ h → (map-equiv h ∘ map-equiv e) ~ (map-equiv f ∘ map-equiv h))
          by equiv-tot (λ h → equiv-inv-htpy _ _ ∘e (baz (map-equiv h) (map-equiv f) (map-equiv h) e))
      where
        [i] : descent-data-circle l2
        [i] = ( descent-data-circle-dependent-pair-type
            ( l)
            ( λ t → A t → B t)
            ( descent-data-circle-function-type l A P αH B Q βK)
            ( eq-descent-data-circle-function-type l A P αH B Q βK)
            ( λ t f → is-equiv f)
            bar
            ((λ f → {!!}) , λ f is-equiv-f → center (is-property-is-equiv _ _ _)))
        [ii] : Eq-descent-data-circle [i] (ev-descent-data-circle l (λ t → A t ≃ B t))
        [ii] = eq-descent-data-circle-dependent-pair-type l _ _ _ _ _ _
```
