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
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
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
`(X, e)` is called **descent data** for the circle.

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

  map-descent-data-circle : type-descent-data-circle → type-descent-data-circle
  map-descent-data-circle = map-equiv aut-descent-data-circle
```

### Dependent descent data for the circle

The equivalence extends to the dependent case, where given a type family `A`
over the circle with descent data `(X, e)`, a type family
`B : (t : 𝕊¹) → A t → U` is equivalent to a type family `R : X → U` equipped
with a family of equivalences `K : (x : X) → R(x) ≃ R(e(x))`. The pair `(R, K)`
is called **dependent descent data** for the circle. Intuitively, this states
that the types over points of `X` belonging to the same connected component in
the total space `Σ 𝕊¹ A` are equivalent.

```agda
dependent-descent-data-circle :
  { l1 : Level} → descent-data-circle l1 →
  ( l2 : Level) → UU (l1 ⊔ lsuc l2)
dependent-descent-data-circle P l2 =
  Σ ( type-descent-data-circle P → UU l2)
    ( λ R → equiv-fam R (R ∘ (map-descent-data-circle P)))

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
        ( map-descent-data-circle P))
  equiv-dependent-descent-data-circle = pr2 Q

  map-equiv-dependent-descent-data-circle :
    ( x : type-descent-data-circle P) →
    ( type-dependent-descent-data-circle x) →
    ( type-dependent-descent-data-circle (map-descent-data-circle P x))
  map-equiv-dependent-descent-data-circle x =
    map-equiv (equiv-dependent-descent-data-circle x)
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
        ( map-descent-data-circle P)
        ( map-descent-data-circle Q)
        ( h))
```

### Canonical descent data for a family over the circle

A type family over the circle gives rise to its canonical descent data, obtained
by evaluation at `base` and transporting along `loop`.

```agda
ev-descent-data-circle :
  { l1 l2 : Level} {S : UU l1} (l : free-loop S) →
  ( S → UU l2) → descent-data-circle l2
pr1 (ev-descent-data-circle l A) = A (base-free-loop l)
pr2 (ev-descent-data-circle l A) = equiv-tr A (loop-free-loop l)
```

### The identity type of descent data

An equivalence between `(X, e)` and `(Y, f)` is a homomorphism between them,
where the underlying map is an equivalence.

```agda
Eq-descent-data-circle :
  { l1 l2 : Level} → descent-data-circle l1 → descent-data-circle l2 →
  UU (l1 ⊔ l2)
Eq-descent-data-circle P Q =
  Σ ( type-descent-data-circle P ≃ type-descent-data-circle Q)
    ( λ h →
      coherence-square-maps
        ( map-equiv h)
        ( map-descent-data-circle P)
        ( map-descent-data-circle Q)
        ( map-equiv h))

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( αH : Eq-descent-data-circle P Q)
  where

  equiv-Eq-descent-data-circle :
    type-descent-data-circle P ≃ type-descent-data-circle Q
  equiv-Eq-descent-data-circle = pr1 αH

  map-Eq-descent-data-circle :
    type-descent-data-circle P → type-descent-data-circle Q
  map-Eq-descent-data-circle = map-equiv equiv-Eq-descent-data-circle

  coherence-square-Eq-descent-data-circle :
    coherence-square-maps
      ( map-equiv equiv-Eq-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-equiv equiv-Eq-descent-data-circle)
  coherence-square-Eq-descent-data-circle = pr2 αH
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
  { l1 l2 : Level} {S : UU l1} {l : free-loop S}
  ( A : family-with-descent-data-circle l l2)
  where

  family-family-with-descent-data-circle : S → UU l2
  family-family-with-descent-data-circle = pr1 A

  descent-data-for-family-with-descent-data-circle :
    descent-data-circle-for-family l
      family-family-with-descent-data-circle
  descent-data-for-family-with-descent-data-circle = pr2 A

  descent-data-family-with-descent-data-circle : descent-data-circle l2
  descent-data-family-with-descent-data-circle =
    pr1 descent-data-for-family-with-descent-data-circle

  type-family-with-descent-data-circle : UU l2
  type-family-with-descent-data-circle =
    type-descent-data-circle descent-data-family-with-descent-data-circle

  aut-family-with-descent-data-circle : Aut type-family-with-descent-data-circle
  aut-family-with-descent-data-circle =
    aut-descent-data-circle descent-data-family-with-descent-data-circle

  map-aut-family-with-descent-data-circle :
    type-family-with-descent-data-circle → type-family-with-descent-data-circle
  map-aut-family-with-descent-data-circle =
    map-descent-data-circle descent-data-family-with-descent-data-circle

  eq-family-with-descent-data-circle :
    Eq-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( ev-descent-data-circle l family-family-with-descent-data-circle)
  eq-family-with-descent-data-circle =
    pr2 descent-data-for-family-with-descent-data-circle

  equiv-family-with-descent-data-circle :
    type-family-with-descent-data-circle ≃
    family-family-with-descent-data-circle (base-free-loop l)
  equiv-family-with-descent-data-circle =
    equiv-Eq-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( ev-descent-data-circle l family-family-with-descent-data-circle)
      ( eq-family-with-descent-data-circle)

  map-equiv-family-with-descent-data-circle :
    type-family-with-descent-data-circle →
    family-family-with-descent-data-circle (base-free-loop l)
  map-equiv-family-with-descent-data-circle =
    map-equiv equiv-family-with-descent-data-circle

  coherence-square-family-with-descent-data-circle :
    coherence-square-maps
      ( map-equiv-family-with-descent-data-circle)
      ( map-aut-family-with-descent-data-circle)
      ( tr family-family-with-descent-data-circle (loop-free-loop l))
      ( map-equiv-family-with-descent-data-circle)
  coherence-square-family-with-descent-data-circle =
    coherence-square-Eq-descent-data-circle
      ( descent-data-family-with-descent-data-circle)
      ( ev-descent-data-circle l family-family-with-descent-data-circle)
      ( eq-family-with-descent-data-circle)

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
        ( map-descent-data-circle P)
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
```
