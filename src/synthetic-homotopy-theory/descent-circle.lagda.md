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
open import foundation.functoriality-dependent-function-types
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

### Fixpoints of descent data

A fixpoint of `(X, e)` is a fixpoint of `e`.

```agda
fixpoint-descent-data-circle :
  { l1 : Level}
  ( P : descent-data-circle l1) → UU l1
fixpoint-descent-data-circle P =
  Σ ( type-descent-data-circle P)
    ( λ x → (map-equiv (aut-descent-data-circle P) x) ＝ x)
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

A type family over the circle gives rise to its canonical descent data, given by
evaluation at `base` and transport along `loop`.

```agda
ev-descent-data-circle :
  { l1 l2 : Level} {S : UU l1} (l : free-loop S) →
  ( S → UU l2) → descent-data-circle l2
pr1 (ev-descent-data-circle l P) = P (base-free-loop l)
pr2 (ev-descent-data-circle l P) = equiv-tr P (loop-free-loop l)
```

### The identity type of descent data

An equivalence between `(X, e)` and `(Y, f)` is a homomorphism between them,
where the underlying map is an equivalence.

```agda
Eq-descent-data-circle :
  { l1 l2 : Level} → descent-data-circle l1 → descent-data-circle l2 →
  UU (l1 ⊔ l2)
Eq-descent-data-circle P Q =
  Σ ( (type-descent-data-circle P) ≃ (type-descent-data-circle Q))
    ( λ h →
      coherence-square-maps
        ( map-equiv h)
        ( map-equiv (aut-descent-data-circle P))
        ( map-equiv (aut-descent-data-circle Q))
        ( map-equiv h))

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P Q)
  where

  equiv-Eq-descent-data-circle :
    type-descent-data-circle P ≃ type-descent-data-circle Q
  equiv-Eq-descent-data-circle = pr1 αH

  coherence-Eq-descent-data-circle :
    coherence-square-maps
      ( map-equiv equiv-Eq-descent-data-circle)
      ( map-equiv (aut-descent-data-circle P))
      ( map-equiv (aut-descent-data-circle Q))
      ( map-equiv equiv-Eq-descent-data-circle)
  coherence-Eq-descent-data-circle = pr2 αH
```

### A family over the circle equipped with corresponding descent data

A family for descent data `(X, e)` is a family over the circle, along with a
proof that they are equivalent.

Descent data for a family `A` is descent data with a proof that it's equivalent
to `A`.

A family with descent data is a family `A` over the circle, equipped with
descent data `(X, e)`, and a proof of their equivalence.

Ideally, every section characterizing descent data of a particular type family
should include a term of type `family-with-descent-data-circle`, whose type
family is the one being described.

Note on naming: a `-for-` in a name indicates that the particular term contains
a proof that it's somehow equivalent to the structure it's "for".

```agda
module _
  { l1 : Level} {S : UU l1} (l : free-loop S)
  where

  family-for-descent-data-circle :
    { l2 : Level} → descent-data-circle l2 → UU (l1 ⊔ lsuc l2)
  family-for-descent-data-circle {l2} P =
    Σ ( S → UU l2)
      ( λ A →
        Eq-descent-data-circle
          ( P)
          ( ev-descent-data-circle l A))

  descent-data-circle-for-family :
    { l2 : Level} → (S → UU l2) → UU (lsuc l2)
  descent-data-circle-for-family {l2} A =
    Σ ( descent-data-circle l2)
      ( λ P →
        Eq-descent-data-circle
          ( P)
          ( ev-descent-data-circle l A))

  family-with-descent-data-circle :
    ( l2 : Level) → UU (l1 ⊔ lsuc l2)
  family-with-descent-data-circle l2 =
    Σ ( S → UU l2) descent-data-circle-for-family

module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  where

  family-family-with-descent-data-circle : S → UU l2
  family-family-with-descent-data-circle = pr1 APαH

  descent-data-for-family-with-descent-data-circle :
    descent-data-circle-for-family l
      family-family-with-descent-data-circle
  descent-data-for-family-with-descent-data-circle = pr2 APαH

  descent-data-family-with-descent-data-circle : descent-data-circle l2
  descent-data-family-with-descent-data-circle =
    pr1 descent-data-for-family-with-descent-data-circle

  eq-family-with-descent-data-circle :
    Eq-descent-data-circle
      descent-data-family-with-descent-data-circle
      ( ev-descent-data-circle l family-family-with-descent-data-circle)
  eq-family-with-descent-data-circle =
    pr2 descent-data-for-family-with-descent-data-circle

  family-for-family-with-descent-data-circle :
    family-for-descent-data-circle l
      descent-data-family-with-descent-data-circle
  pr1 family-for-family-with-descent-data-circle =
    family-family-with-descent-data-circle
  pr2 family-for-family-with-descent-data-circle =
    eq-family-with-descent-data-circle
```

## Properties

### Characterization of the identity type of descent data for the circle

```agda
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

  Eq-dependent-descent-data-circle :
    dependent-descent-data-circle P l2 → dependent-descent-data-circle P l2
    → UU (l1 ⊔ l2)
  Eq-dependent-descent-data-circle Q T =
    Σ ( equiv-fam
        ( type-dependent-descent-data-circle P Q)
        ( type-dependent-descent-data-circle P T))
      ( λ H →
        ( x : type-descent-data-circle P) →
        coherence-square-maps
          ( map-equiv (H x))
          ( map-equiv (equiv-dependent-descent-data-circle P Q x))
          ( map-equiv (equiv-dependent-descent-data-circle P T x))
          ( map-equiv (H (map-equiv (aut-descent-data-circle P) x))))

  refl-Eq-dependent-descent-data-circle :
    ( Q : dependent-descent-data-circle P l2) →
    Eq-dependent-descent-data-circle Q Q
  pr1 (refl-Eq-dependent-descent-data-circle Q) =
    id-equiv-fam (type-dependent-descent-data-circle P Q)
  pr2 (refl-Eq-dependent-descent-data-circle Q) x = refl-htpy

  Eq-eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle P l2) →
    Q ＝ T → Eq-dependent-descent-data-circle Q T
  Eq-eq-dependent-descent-data-circle Q .Q refl =
    refl-Eq-dependent-descent-data-circle Q

  is-contr-total-Eq-dependent-descent-data-circle :
    ( Q : dependent-descent-data-circle P l2) →
    is-contr
      ( Σ ( dependent-descent-data-circle P l2)
          ( Eq-dependent-descent-data-circle Q))
  is-contr-total-Eq-dependent-descent-data-circle Q =
    is-contr-total-Eq-structure
      ( λ R K H →
        ( x : type-descent-data-circle P) →
        coherence-square-maps
          ( map-equiv (H x))
          ( map-equiv (equiv-dependent-descent-data-circle P Q x))
          ( map-equiv (K x))
          ( map-equiv (H (map-equiv (aut-descent-data-circle P) x))))
      ( is-contr-total-equiv-fam (type-dependent-descent-data-circle P Q))
      ( type-dependent-descent-data-circle P Q ,
        id-equiv-fam (type-dependent-descent-data-circle P Q))
      ( is-contr-total-Eq-Π
        ( λ x K →
          ( map-equiv (equiv-dependent-descent-data-circle P Q x)) ~
          ( map-equiv K))
        ( λ x →
          is-contr-total-htpy-equiv
            ( equiv-dependent-descent-data-circle P Q x)))

  is-equiv-Eq-eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle P l2) →
    is-equiv (Eq-eq-dependent-descent-data-circle Q T)
  is-equiv-Eq-eq-dependent-descent-data-circle Q =
    fundamental-theorem-id
      ( is-contr-total-Eq-dependent-descent-data-circle Q)
      ( Eq-eq-dependent-descent-data-circle Q)

  eq-Eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle P l2) →
    Eq-dependent-descent-data-circle Q T → Q ＝ T
  eq-Eq-dependent-descent-data-circle Q T =
    map-inv-is-equiv (is-equiv-Eq-eq-dependent-descent-data-circle Q T)
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
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  where

  triangle-comparison-descent-data-circle :
    coherence-triangle-maps
      ( ev-descent-data-circle l)
      ( comparison-descent-data-circle l2)
      ( ev-free-loop l (UU l2))
  triangle-comparison-descent-data-circle A =
    eq-Eq-descent-data-circle
      ( ev-descent-data-circle l A)
      ( comparison-descent-data-circle l2 (ev-free-loop l (UU l2) A))
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

  descent-data-circle-family : (S → UU l2) → UU (lsuc l2)
  descent-data-circle-family A =
    Σ ( descent-data-circle l2)
      ( λ P → Eq-descent-data-circle P (ev-descent-data-circle l A))

unique-family-property-circle :
  { l1 : Level} (l2 : Level) {S : UU l1} (l : free-loop S) →
  UU (l1 ⊔ lsuc l2)
unique-family-property-circle l2 {S} l =
  ( Q : descent-data-circle l2) → is-contr (family-for-descent-data-circle l Q)

module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
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

  family-with-descent-data-circle-descent-data :
    descent-data-circle l2 →
    universal-property-circle (lsuc l2) l →
    family-with-descent-data-circle l l2
  family-with-descent-data-circle-descent-data P up-circle =
    (pr1 associated-family , P , pr2 associated-family)
    where
      associated-family : family-for-descent-data-circle l P
      associated-family =
        center ( unique-family-property-universal-property-circle up-circle P)
```

### Uniqueness of dependent descent data characterizing a type family over a family over the circle

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  where

  private
    A : S → UU l2
    A = family-family-with-descent-data-circle l APαH
    P : descent-data-circle l2
    P = descent-data-family-with-descent-data-circle l APαH
    αH : Eq-descent-data-circle P (ev-descent-data-circle l A)
    αH = eq-family-with-descent-data-circle l APαH
    α : type-descent-data-circle P ≃ A (base-free-loop l)
    α = equiv-Eq-descent-data-circle P (ev-descent-data-circle l A) αH
    e : Aut (type-descent-data-circle P)
    e = aut-descent-data-circle P
    H : coherence-square-maps
          ( map-equiv α)
          ( map-equiv e)
          ( tr A (loop-free-loop l))
          ( map-equiv α)
    H = coherence-Eq-descent-data-circle P (ev-descent-data-circle l A) αH

  comparison-dependent-descent-data-circle :
    free-dependent-loop l (λ t → (A t → UU l3)) ≃
    dependent-descent-data-circle P l3
  comparison-dependent-descent-data-circle =
    equiv-Σ
      ( λ R → equiv-fam R (R ∘ (map-equiv e)))
      ( equiv-precomp α (UU l3))
      ( λ R →
        equivalence-reasoning
          ( (tr (λ t → A t → UU l3) (loop-free-loop l) R ＝ R))
          ≃ ( (tr (λ _ → UU l3) (loop-free-loop l) ∘ R) ~
              (R ∘ (tr A (loop-free-loop l))))
            by
              inv-equiv
                ( compute-path-over-function-type
                  ( A)
                  ( λ _ → UU l3)
                  ( loop-free-loop l)
                  ( R)
                  ( R))
          ≃ (R ~ (R ∘ (tr A (loop-free-loop l))))
            by
              equiv-concat-htpy
                ( (inv-htpy (tr-const (loop-free-loop l))) ·r R)
                ( (R ∘ (tr A (loop-free-loop l))))
          ≃ equiv-fam
              ( R ∘ map-equiv α)
              ( R ∘ (map-equiv α ∘ (map-equiv e)))
            by
              inv-equiv
                ( equiv-Π
                  ( eq-value R (R ∘ tr A (loop-free-loop l)))
                  ( α)
                  ( λ a' →
                    ( equiv-concat'
                      ( R (map-equiv α a'))
                      ( ap R (H a'))) ∘e
                    ( inv-equiv equiv-univalence))))

  ev-dependent-descent-data-circle :
    ((x : S) → (A x) → UU l3) → dependent-descent-data-circle P l3
  pr1 (ev-dependent-descent-data-circle A) =
    A (base-free-loop l) ∘ map-equiv α
  pr2 (ev-dependent-descent-data-circle A) x =
    equiv-tr (ind-Σ A) (eq-pair-Σ (loop-free-loop l) (inv (H x)))

  triangle-comparison-dependent-descent-data-circle :
    coherence-triangle-maps
      ( ev-dependent-descent-data-circle)
      ( map-equiv comparison-dependent-descent-data-circle)
      ( ev-free-loop-Π l (λ t → A t → UU l3))
  triangle-comparison-dependent-descent-data-circle B =
    eq-Eq-dependent-descent-data-circle P
      ( ev-dependent-descent-data-circle B)
      ( map-equiv comparison-dependent-descent-data-circle
        ( ev-free-loop-Π l (λ t → A t → UU l3) B))
      ( id-equiv-fam _ ,
        λ x a →
        -- REWRITE & REFORMAT
        equational-reasoning
          tr (ind-Σ A) (eq-pair-Σ (loop-free-loop l) (inv (pr2 αH x))) a
          ＝ {!!}
            by {!!}
          ＝ map-equiv
              ( map-inv-equiv
                ( equiv-Π
                  ( λ x →
                    Id (A (pr1 l) x) (A (pr1 l) (tr Q (pr2 l) x))) (pr1 αH)
                ( λ a' →
                  equiv-comp
                    ( equiv-concat' (A (pr1 l) (pr1 (pr1 αH) a'))
                    ( ap (A (pr1 l)) (pr2 αH a')))
                    ( inv-equiv equiv-univalence)))
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

  is-equiv-ev-dependent-descent-data-circle-dependent-universal-property-circle :
    dependent-universal-property-circle (l2 ⊔ lsuc l3) l →
    is-equiv ev-dependent-descent-data-circle
  is-equiv-ev-dependent-descent-data-circle-dependent-universal-property-circle
    dup-circle =
      is-equiv-comp-htpy
        ( ev-dependent-descent-data-circle)
        ( map-equiv comparison-dependent-descent-data-circle)
        ( ev-free-loop-Π l (λ t → A t → UU l3))
        ( triangle-comparison-dependent-descent-data-circle)
        ( dup-circle (λ t → A t → UU l3))
        ( is-equiv-map-equiv comparison-dependent-descent-data-circle)

  family-dependent-descent-data-circle :
    dependent-descent-data-circle P l3 → UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-dependent-descent-data-circle Q =
    Σ ( (x : S) → A x → UU l3)
      ( λ R →
        Eq-dependent-descent-data-circle P Q
          ( ev-dependent-descent-data-circle R))

  unique-dependent-family-property-circle : UU (l1 ⊔ l2 ⊔ lsuc l3)
  unique-dependent-family-property-circle =
    ( Q : dependent-descent-data-circle P l3) →
    is-contr (family-dependent-descent-data-circle Q)

  unique-dependent-family-property-dependent-universal-property-circle :
    dependent-universal-property-circle (l2 ⊔ lsuc l3) l →
    unique-dependent-family-property-circle
  unique-dependent-family-property-dependent-universal-property-circle
    dup-circle Q =
      is-contr-is-equiv'
        ( fib ev-dependent-descent-data-circle Q)
        ( tot
          ( λ B →
            ( Eq-eq-dependent-descent-data-circle P Q
              ( ev-dependent-descent-data-circle B)) ∘
            ( inv)))
        ( is-equiv-tot-is-fiberwise-equiv
          ( λ B →
            is-equiv-comp _ _
              ( is-equiv-inv _ _)
              ( is-equiv-Eq-eq-dependent-descent-data-circle P
                ( Q)
                ( ev-dependent-descent-data-circle B))))
        ( is-contr-map-is-equiv
          ( is-equiv-ev-dependent-descent-data-circle-dependent-universal-property-circle
            ( dup-circle))
          ( Q))
```

### Characterization of sections of type families over the circle

Sections of type families over the circle are exactly the fixpoints of the
automorphism from the characteristic descent data.

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  where

  private
    A : S → UU l2
    A = family-family-with-descent-data-circle l APαH
    P : descent-data-circle l2
    P = descent-data-family-with-descent-data-circle l APαH
    αH : Eq-descent-data-circle P (ev-descent-data-circle l A)
    αH = eq-family-with-descent-data-circle l APαH
    α : type-descent-data-circle P ≃ A (base-free-loop l)
    α = equiv-Eq-descent-data-circle P (ev-descent-data-circle l A) αH

  map-compute-path-over-loop-circle :
    ( x y : type-descent-data-circle P) →
    ( map-equiv (aut-descent-data-circle P) x ＝ y) →
    ( path-over A (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  map-compute-path-over-loop-circle x y q =
    inv (coherence-Eq-descent-data-circle P (ev-descent-data-circle l A) αH x) ∙
    ( ap (map-equiv α) q)

  is-equiv-map-compute-path-over-loop-circle :
    ( x y : type-descent-data-circle P) →
    is-equiv (map-compute-path-over-loop-circle x y)
  is-equiv-map-compute-path-over-loop-circle x y =
    fundamental-theorem-id
      ( is-contr-equiv'
        ( fib (map-equiv α) (tr A (loop-free-loop l) (map-equiv α x)))
        ( equiv-fib _ _)
        ( is-contr-map-is-equiv
          ( is-equiv-map-equiv α)
          ( tr A (loop-free-loop l) (map-equiv α x))))
      ( map-compute-path-over-loop-circle x)
      ( y)

  compute-path-over-loop-circle :
    ( x y : type-descent-data-circle P) →
    ( map-equiv (aut-descent-data-circle P) x ＝ y) ≃
    ( path-over A (loop-free-loop l) (map-equiv α x) (map-equiv α y))
  pr1 (compute-path-over-loop-circle x y) =
    map-compute-path-over-loop-circle x y
  pr2 (compute-path-over-loop-circle x y) =
    is-equiv-map-compute-path-over-loop-circle x y
```

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  where

  private
    A : S → UU l2
    A = family-family-with-descent-data-circle l APαH
    P : descent-data-circle l2
    P = descent-data-family-with-descent-data-circle l APαH
    αH : Eq-descent-data-circle P (ev-descent-data-circle l A)
    αH = eq-family-with-descent-data-circle l APαH
    α : type-descent-data-circle P ≃ A (base-free-loop l)
    α = equiv-Eq-descent-data-circle P (ev-descent-data-circle l A) αH

  ev-fixpoint-descent-data-circle :
    ( (x : S) → A x) → fixpoint-descent-data-circle P
  pr1 (ev-fixpoint-descent-data-circle s) =
    map-inv-equiv
      ( α)
      ( s (base-free-loop l))
  pr2 (ev-fixpoint-descent-data-circle s) =
    map-inv-is-equiv
      ( is-equiv-map-compute-path-over-loop-circle
        ( l)
        ( APαH)
        ( map-inv-equiv α (s (base-free-loop l)))
        ( map-inv-equiv α (s (base-free-loop l))))
      ( ( ap
          ( tr A (loop-free-loop l))
          ( issec-map-inv-equiv α (s (base-free-loop l)))) ∙
        ( ( apd s (loop-free-loop l)) ∙
          ( inv (issec-map-inv-equiv α (s (base-free-loop l))))))

  equiv-fixpoint-descent-data-circle-free-dependent-loop :
    fixpoint-descent-data-circle P ≃ free-dependent-loop l A
  equiv-fixpoint-descent-data-circle-free-dependent-loop =
    equiv-Σ
      ( λ x → path-over A (loop-free-loop l) x x)
      ( α)
      ( λ x → compute-path-over-loop-circle l APαH x x)

  comparison-fixpoint-descent-data-circle :
    fixpoint-descent-data-circle P → free-dependent-loop l A
  comparison-fixpoint-descent-data-circle =
    map-equiv equiv-fixpoint-descent-data-circle-free-dependent-loop

  triangle-comparison-fixpoint-descent-data-circle :
    coherence-triangle-maps
      ( ev-free-loop-Π l A)
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
  triangle-comparison-fixpoint-descent-data-circle s =
    eq-Eq-free-dependent-loop l A
      ( ev-free-loop-Π l A s)
      ( ( comparison-fixpoint-descent-data-circle ∘
          ev-fixpoint-descent-data-circle)
        ( s))
      ( inv issec-inv-α ,
        inv
        ( ( horizontal-concat-Id²
            ( refl {x = ap (tr A (loop-free-loop l)) (inv issec-inv-α)})
            ( issec-map-inv-is-equiv
              ( is-equiv-map-compute-path-over-loop-circle
                ( l)
                ( APαH)
                ( map-inv-equiv α (s (base-free-loop l)))
                ( pr1 (ev-fixpoint-descent-data-circle s)))
              ( _))) ∙
          ( ( inv (assoc (ap _ (inv issec-inv-α)) _ _)) ∙
            ( horizontal-concat-Id²
              ( inv
                ( ap-concat-eq (tr A (loop-free-loop l))
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
      ( ev-free-loop-Π l A)
      ( comparison-fixpoint-descent-data-circle)
      ( ev-fixpoint-descent-data-circle)
      ( triangle-comparison-fixpoint-descent-data-circle)
      ( is-equiv-comparison-fixpoint-descent-data-circle)
      ( dup-circle A)

  equiv-ev-fixpoint-descent-data-circle :
    ( dependent-universal-property-circle l2 l) →
    ( (x : S) → A x) ≃ (fixpoint-descent-data-circle P)
  pr1 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    ev-fixpoint-descent-data-circle
  pr2 (equiv-ev-fixpoint-descent-data-circle dup-circle) =
    is-equiv-ev-fixpoint-descent-data-circle dup-circle

  compute-ev-fixpoint-descent-data-circle :
    coherence-square-maps
      ( ev-fixpoint-descent-data-circle)
      ( ev-point (base-free-loop l) {A})
      ( pr1)
      ( map-inv-equiv α)
  compute-ev-fixpoint-descent-data-circle = refl-htpy
```

### Characterization of families of maps over the circle

Families of maps over the circle are maps commuting with the respective
automorphisms.

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  ( BQβK : family-with-descent-data-circle l l3)
  where

  private
    A : S → UU l2
    A = family-family-with-descent-data-circle l APαH
    P : descent-data-circle l2
    P = descent-data-family-with-descent-data-circle l APαH
    X : UU l2
    X = type-descent-data-circle P
    e : Aut X
    e = aut-descent-data-circle P
    αH : Eq-descent-data-circle P (ev-descent-data-circle l A)
    αH = eq-family-with-descent-data-circle l APαH
    α : X ≃ A (base-free-loop l)
    α = equiv-Eq-descent-data-circle P (ev-descent-data-circle l A) αH

    B : S → UU l3
    B = family-family-with-descent-data-circle l BQβK
    Q : descent-data-circle l3
    Q = descent-data-family-with-descent-data-circle l BQβK
    Y : UU l3
    Y = type-descent-data-circle Q
    f : Aut Y
    f = aut-descent-data-circle Q
    βK : Eq-descent-data-circle Q (ev-descent-data-circle l B)
    βK = eq-family-with-descent-data-circle l BQβK
    β : Y ≃ B (base-free-loop l)
    β = equiv-Eq-descent-data-circle Q (ev-descent-data-circle l B) βK

  descent-data-circle-function-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-function-type =
    X → Y
  pr2 descent-data-circle-function-type =
    (equiv-postcomp X f) ∘e (equiv-precomp (inv-equiv e) Y)

  eq-descent-data-circle-function-type :
    Eq-descent-data-circle
      ( descent-data-circle-function-type)
      ( ev-descent-data-circle l (λ s → (A s → B s)))
  pr1 eq-descent-data-circle-function-type =
    (equiv-postcomp (A (base-free-loop l)) β) ∘e (equiv-precomp (inv-equiv α) Y)
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

  descent-data-circle-family-function-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  pr1 descent-data-circle-family-function-type =
    λ t → A t → B t
  pr1 (pr2 descent-data-circle-family-function-type) =
    descent-data-circle-function-type
  pr2 (pr2 descent-data-circle-family-function-type) =
    eq-descent-data-circle-function-type

  equiv-fixpoint-descent-data-circle-function-type-hom :
    fixpoint-descent-data-circle descent-data-circle-function-type ≃
    hom-descent-data-circle P Q
  equiv-fixpoint-descent-data-circle-function-type-hom =
    equiv-tot
      ( λ h →
        ( equiv-inv-htpy (((map-equiv f) ∘ h)) (h ∘ (map-equiv e))) ∘e
        ( ( inv-equiv
            ( equiv-coherence-triangle-maps-inv-top ((map-equiv f) ∘ h) h e)) ∘e
          ( equiv-funext)))

  equiv-ev-descent-data-circle-function-type-hom :
    dependent-universal-property-circle (l2 ⊔ l3) l →
    ( (s : S) → A s → B s) ≃ (hom-descent-data-circle P Q)
  equiv-ev-descent-data-circle-function-type-hom dup-circle =
    equiv-fixpoint-descent-data-circle-function-type-hom ∘e
    ( equiv-ev-fixpoint-descent-data-circle
      ( l)
      ( descent-data-circle-family-function-type)
      ( dup-circle))
```

### Characterization of descent data for various types

#### Descent data for constant families

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( X : UU l2)
  where

  descent-data-circle-constant-type : descent-data-circle l2
  pr1 descent-data-circle-constant-type = X
  pr2 descent-data-circle-constant-type = id-equiv

  eq-descent-data-circle-constant-type :
    Eq-descent-data-circle
      ( descent-data-circle-constant-type)
      ( ev-descent-data-circle l (λ _ → X))
  pr1 eq-descent-data-circle-constant-type =
    id-equiv
  pr2 eq-descent-data-circle-constant-type =
    inv-htpy (tr-const (loop-free-loop l))

  descent-data-circle-family-constant-type :
    family-with-descent-data-circle l l2
  pr1 descent-data-circle-family-constant-type =
    λ _ → X
  pr1 (pr2 descent-data-circle-family-constant-type) =
    descent-data-circle-constant-type
  pr2 (pr2 descent-data-circle-family-constant-type) =
    eq-descent-data-circle-constant-type
```

#### Descent data for dependent pair types

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  ( B : (x : S) → (family-family-with-descent-data-circle l APαH x) → UU l3)
  ( Q :
    dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle l APαH)
      ( l3))
  ( βK :
    Eq-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle l APαH)
      ( Q)
      ( ev-dependent-descent-data-circle l APαH B))
  where

  private
    A : S → UU l2
    A = family-family-with-descent-data-circle l APαH
    P : descent-data-circle l2
    P = descent-data-family-with-descent-data-circle l APαH
    αH : Eq-descent-data-circle P (ev-descent-data-circle l A)
    αH = eq-family-with-descent-data-circle l APαH
    X : UU l2
    X = type-descent-data-circle P
    e : X ≃ X
    e = aut-descent-data-circle P
    α : X ≃ A (base-free-loop l)
    α = equiv-Eq-descent-data-circle P (ev-descent-data-circle l A) αH

    R : X → UU l3
    R = type-dependent-descent-data-circle P Q
    β : (x : X) → (R x) ≃ (B (base-free-loop l) (map-equiv α x))
    β = pr1 βK
    β' : (x : X) → (R x) → (B (base-free-loop l) (map-equiv α x))
    β' x = map-equiv (β x)
    K : (x : X) → (R x) ≃ (R (map-equiv e x))
    K = equiv-dependent-descent-data-circle P Q

  descent-data-circle-dependent-pair-type : descent-data-circle (l2 ⊔ l3)
  pr1 descent-data-circle-dependent-pair-type = Σ X R
  pr2 descent-data-circle-dependent-pair-type = equiv-Σ R e K

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
          by
            tr-Σ
              ( B)
              ( loop-free-loop l)
              ( map-Σ (B (base-free-loop l)) (map-equiv α) β' u)
        ＝ ( map-equiv α (map-equiv e (pr1 u))) ,
            map-equiv
              ( β (map-equiv e (pr1 u)))
              ( map-equiv
                ( equiv-dependent-descent-data-circle P Q (pr1 u))
                ( pr2 u))
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

  descent-data-circle-family-dependent-pair-type :
    family-with-descent-data-circle l (l2 ⊔ l3)
  pr1 descent-data-circle-family-dependent-pair-type =
    λ t → Σ (A t) (B t)
  pr1 (pr2 descent-data-circle-family-dependent-pair-type) =
    descent-data-circle-dependent-pair-type
  pr2 (pr2 descent-data-circle-family-dependent-pair-type) =
    eq-descent-data-circle-dependent-pair-type
```

### Characterization of equivalences between families over the circle

```agda
baz : {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
      (f : B → C) (g : C → D) (h : A → D) (e : B ≃ A) →
      ((g ∘ (f ∘ (map-inv-equiv e))) ~ h) ≃ ((g ∘ f) ~ (h ∘ (map-equiv e)))
baz f g h e =
  inv-equiv (equiv-coherence-triangle-maps-inv-top (g ∘ f) h e)

module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( APαH : family-with-descent-data-circle l l2)
  ( BQβK : family-with-descent-data-circle l l2)
  where

  private
    A : S → UU l2
    A = family-family-with-descent-data-circle l APαH
    P : descent-data-circle l2
    P = descent-data-family-with-descent-data-circle l APαH
    X : UU l2
    X = type-descent-data-circle P
    e : Aut X
    e = aut-descent-data-circle P
    αH : Eq-descent-data-circle P (ev-descent-data-circle l A)
    αH = eq-family-with-descent-data-circle l APαH
    α : X ≃ A (base-free-loop l)
    α = equiv-Eq-descent-data-circle P (ev-descent-data-circle l A) αH

    B : S → UU l2
    B = family-family-with-descent-data-circle l BQβK
    Q : descent-data-circle l2
    Q = descent-data-family-with-descent-data-circle l BQβK
    Y : UU l2
    Y = type-descent-data-circle Q
    f : Aut Y
    f = aut-descent-data-circle Q
    βK : Eq-descent-data-circle Q (ev-descent-data-circle l B)
    βK = eq-family-with-descent-data-circle l BQβK
    β : Y ≃ B (base-free-loop l)
    β = equiv-Eq-descent-data-circle Q (ev-descent-data-circle l B) βK

  descent-data-circle-is-equiv :
    dependent-descent-data-circle
      ( descent-data-circle-function-type l APαH BQβK)
      ( l2)
  pr1 descent-data-circle-is-equiv h = is-equiv h
  pr2 descent-data-circle-is-equiv h =
    ( equiv-is-equiv-postcomp-is-equiv
      ( h ∘ map-inv-equiv (aut-descent-data-circle P))
      ( aut-descent-data-circle Q)) ∘e
    ( equiv-is-equiv-precomp-is-equiv
      ( inv-equiv (aut-descent-data-circle P))
      ( h))

  foo :
    ( {k : Level} → dependent-universal-property-circle k l) →
    equiv-fam A B ≃ Eq-descent-data-circle P Q
  foo dup-circle =
    equivalence-reasoning
      ( (t : S) → (A t) ≃ (B t))
      ≃ fixpoint-descent-data-circle
          ( descent-data-family-with-descent-data-circle l underlying-dd)
        by equiv-ev-fixpoint-descent-data-circle l underlying-dd dup-circle
      ≃ Σ ( X ≃ Y)
          ( λ h →
            ( map-equiv f ∘ (map-equiv h ∘ (map-inv-equiv e))) ~ (map-equiv h))
        by equiv-tot (λ x → extensionality-equiv _ _)
      ≃ Σ ( X ≃ Y)
          ( λ h → (map-equiv h ∘ map-equiv e) ~ (map-equiv f ∘ map-equiv h))
        by
          equiv-tot
            ( λ h →
              ( equiv-inv-htpy _ _) ∘e
              ( inv-equiv
                ( equiv-coherence-triangle-maps-inv-top
                  ( map-equiv f ∘ map-equiv h)
                  ( map-equiv h)
                  ( e))))
    where
      underlying-dd : family-with-descent-data-circle l l2
      underlying-dd =
        descent-data-circle-family-dependent-pair-type
          ( l)
          ( descent-data-circle-family-function-type l APαH BQβK)
          ( λ t f → is-equiv f)
          ( descent-data-circle-is-equiv)
          ( ( λ f →
              ( equiv-is-equiv-postcomp-is-equiv (f ∘ map-inv-equiv α) β) ∘e
              ( equiv-is-equiv-precomp-is-equiv (inv-equiv α) f)) ,
            ( λ f is-equiv-f → center (is-property-is-equiv _ _ _)))
```
