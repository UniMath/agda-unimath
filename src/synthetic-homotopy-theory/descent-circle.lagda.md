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
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
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
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-dependent-pair-types
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

By the
[universal property of the circle](synthetic-homotopy-theory.universal-property-circle.md)
and [univalence](foundation.univalence.md), a type family `A : 𝕊¹ → U` over the
[circle](synthetic-homotopy-theory.circle.md) is equivalent to a type `X : U`
equipped with an [automorphism](foundation.automorphisms.md) `e : X ≃ X`, in a
way made precise in further sections of this file. The pair `(X, e)` is called
**descent data** for the circle.

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

### Homomorphisms between descent data for the circle

A homomorphism `h` between `(X, e)` and `(Y, f)` is a map from `X` to `Y` such
that the obvious square [commutes](foundation.commuting-squares-of-maps.md).

```text
      h
  X -----> Y
  |        |
 e|        |f
  v        v
  X -----> Y
      h
```

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

module _
  { l1 l2 : Level} (P : descent-data-circle l1) (Q : descent-data-circle l2)
  ( h : hom-descent-data-circle P Q)
  where

  map-hom-descent-data-circle :
    type-descent-data-circle P → type-descent-data-circle Q
  map-hom-descent-data-circle = pr1 h

  coherence-hom-descent-data-circle :
    coherence-square-maps
      ( map-hom-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-hom-descent-data-circle)
  coherence-hom-descent-data-circle = pr2 h
```

### Canonical descent data for a family over the circle

A type family over the circle gives rise to its canonical descent data, obtained
by evaluation at `base` and
[transporting](foundation-core.transport-along-identifications.md) along `loop`.

```agda
ev-descent-data-circle :
  { l1 l2 : Level} {S : UU l1} (l : free-loop S) →
  ( S → UU l2) → descent-data-circle l2
pr1 (ev-descent-data-circle l A) = A (base-free-loop l)
pr2 (ev-descent-data-circle l A) = equiv-tr A (loop-free-loop l)
```

### The identity type of descent data for the circle

An [equivalence](foundation.equivalences.md) between `(X, e)` and `(Y, f)` is an
equivalence between `X` and `Y` which commutes with the automorphisms.

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
      ( map-Eq-descent-data-circle)
      ( map-descent-data-circle P)
      ( map-descent-data-circle Q)
      ( map-Eq-descent-data-circle)
  coherence-square-Eq-descent-data-circle = pr2 αH
```

### A family over the circle equipped with corresponding descent data

A family for descent data `(X, e)` is a family over the circle, along with a
proof that `(X, e)` is equivalent to the canonical descent data of the family.

Descent data for a family `A : 𝕊¹ → U` is descent data with a proof that it's
equivalent to the canonical descent data of `A`.

A family with descent data is a family `A : 𝕊¹ → U` over the circle, equipped
with descent data `(X, e)`, and a proof of their equivalence. This can be
described as a diagram

```text
      α
  X -----> A base
  |         |
 e|         | tr A loop
  v         v
  X -----> A base
      α
```

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

### Dependent descent data for the circle

The equivalence extends to the dependent case, where given a type family `A`
over the circle with descent data `(X, e)`, a type family
`B : (t : 𝕊¹) → A t → U` is equivalent to a type family `R : X → U` equipped
with a family of equivalences `k : (x : X) → R(x) ≃ R(e(x))`. The pair `(R, k)`
is called **dependent descent data** for the circle over `A`. Intuitively, this
states that the types over points of `X` belonging to the same connected
component in the total space `Σ 𝕊¹ A` are equivalent.

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

  pseudo-aut-dependent-descent-data-circle :
    equiv-fam
      ( type-dependent-descent-data-circle)
      ( type-dependent-descent-data-circle ∘ (map-descent-data-circle P))
  pseudo-aut-dependent-descent-data-circle = pr2 Q

  map-dependent-descent-data-circle :
    ( x : type-descent-data-circle P) →
    ( type-dependent-descent-data-circle x) →
    ( type-dependent-descent-data-circle (map-descent-data-circle P x))
  map-dependent-descent-data-circle x =
    map-equiv (pseudo-aut-dependent-descent-data-circle x)
```

### Canonical dependent descent data for a family over a family over the circle

```agda
ev-dependent-descent-data-circle :
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S) →
  ( A : family-with-descent-data-circle l l2) →
  ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3) →
  dependent-descent-data-circle
    ( descent-data-family-with-descent-data-circle A)
    ( l3)
pr1 (ev-dependent-descent-data-circle l A B) x =
  B (base-free-loop l) (map-equiv-family-with-descent-data-circle A x)
pr2 (ev-dependent-descent-data-circle l A B) x =
  equiv-tr
    ( ind-Σ B)
    ( eq-pair-Σ
      ( loop-free-loop l)
      ( inv (coherence-square-family-with-descent-data-circle A x)))
```

### The identity type of dependent descent data for the circle

```agda
module _
  { l1 l2 l3 : Level} (P : descent-data-circle l1)
  where

  Eq-dependent-descent-data-circle :
    dependent-descent-data-circle P l2 → dependent-descent-data-circle P l3 →
    UU (l1 ⊔ l2 ⊔ l3)
  Eq-dependent-descent-data-circle Q T =
    Σ ( equiv-fam
        ( type-dependent-descent-data-circle P Q)
        ( type-dependent-descent-data-circle P T))
      ( λ H →
        ( x : type-descent-data-circle P) →
        coherence-square-maps
          ( map-equiv (H x))
          ( map-dependent-descent-data-circle P Q x)
          ( map-dependent-descent-data-circle P T x)
          ( map-equiv (H (map-descent-data-circle P x))))

module _
  { l1 l2 l3 : Level} (P : descent-data-circle l1)
  ( Q : dependent-descent-data-circle P l2)
  ( T : dependent-descent-data-circle P l3)
  ( αH : Eq-dependent-descent-data-circle P Q T)
  where

  equiv-Eq-dependent-descent-data-circle :
    equiv-fam
      ( type-dependent-descent-data-circle P Q)
      ( type-dependent-descent-data-circle P T)
  equiv-Eq-dependent-descent-data-circle = pr1 αH

  map-Eq-dependent-descent-data-circle :
    ( x : type-descent-data-circle P) →
    ( type-dependent-descent-data-circle P Q x) →
    ( type-dependent-descent-data-circle P T x)
  map-Eq-dependent-descent-data-circle x =
    map-equiv (equiv-Eq-dependent-descent-data-circle x)

  coherence-square-Eq-dependent-descent-data-circle :
    ( x : type-descent-data-circle P) →
    coherence-square-maps
      ( map-Eq-dependent-descent-data-circle x)
      ( map-dependent-descent-data-circle P Q x)
      ( map-dependent-descent-data-circle P T x)
      ( map-Eq-dependent-descent-data-circle
        ( map-descent-data-circle P x))
  coherence-square-Eq-dependent-descent-data-circle = pr2 αH
```

### A dependent family over the circle with corresponding dependent descent data

```agda
module _
  { l1 l2 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  family-for-dependent-descent-data-circle :
    { l3 : Level} →
    dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( l3) →
    UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-for-dependent-descent-data-circle {l3} Q =
    Σ ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3)
      ( λ B →
        Eq-dependent-descent-data-circle
          ( descent-data-family-with-descent-data-circle A)
          ( Q)
          ( ev-dependent-descent-data-circle l A B))

  dependent-descent-data-circle-for-family :
    { l3 : Level} →
    ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3) →
    UU (l2 ⊔ lsuc l3)
  dependent-descent-data-circle-for-family {l3} B =
    Σ ( dependent-descent-data-circle
        ( descent-data-family-with-descent-data-circle A)
        ( l3))
      ( λ Q →
        Eq-dependent-descent-data-circle
          ( descent-data-family-with-descent-data-circle A)
          ( Q)
          ( ev-dependent-descent-data-circle l A B))

  family-with-dependent-descent-data-circle :
    ( l3 : Level) → UU (l1 ⊔ l2 ⊔ lsuc l3)
  family-with-dependent-descent-data-circle l3 =
    Σ ( (x : S) → (family-family-with-descent-data-circle A x) → UU l3)
      dependent-descent-data-circle-for-family

module _
  { l1 l2 l3 : Level} {S : UU l1} {l : free-loop S}
  ( A : family-with-descent-data-circle l l2)
  ( B : family-with-dependent-descent-data-circle l A l3)
  where

  family-family-with-dependent-descent-data-circle :
    ( x : S) → (family-family-with-descent-data-circle A x) → UU l3
  family-family-with-dependent-descent-data-circle = pr1 B

  dependent-descent-data-for-family-with-dependent-descent-data-circle :
    dependent-descent-data-circle-for-family l A
      family-family-with-dependent-descent-data-circle
  dependent-descent-data-for-family-with-dependent-descent-data-circle = pr2 B

  dependent-descent-data-family-with-dependent-descent-data-circle :
    dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( l3)
  dependent-descent-data-family-with-dependent-descent-data-circle =
    pr1 dependent-descent-data-for-family-with-dependent-descent-data-circle

  type-family-with-dependent-descent-data-circle :
    type-family-with-descent-data-circle A → UU l3
  type-family-with-dependent-descent-data-circle =
    type-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)

  pseudo-aut-family-with-dependent-descent-data-circle :
    equiv-fam
    ( type-family-with-dependent-descent-data-circle)
    ( type-family-with-dependent-descent-data-circle ∘
      ( map-aut-family-with-descent-data-circle A))
  pseudo-aut-family-with-dependent-descent-data-circle =
    pseudo-aut-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)

  map-pseudo-aut-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    ( type-family-with-dependent-descent-data-circle x) →
    ( type-family-with-dependent-descent-data-circle
      ( map-aut-family-with-descent-data-circle A x))
  map-pseudo-aut-family-with-dependent-descent-data-circle =
    map-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)

  eq-family-with-dependent-descent-data-circle :
    Eq-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)
      ( ev-dependent-descent-data-circle l A
        ( family-family-with-dependent-descent-data-circle))
  eq-family-with-dependent-descent-data-circle =
    pr2 dependent-descent-data-for-family-with-dependent-descent-data-circle

  equiv-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    ( type-family-with-dependent-descent-data-circle x) ≃
    ( family-family-with-dependent-descent-data-circle
      ( base-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x))
  equiv-family-with-dependent-descent-data-circle =
    equiv-Eq-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)
      ( ev-dependent-descent-data-circle l A
        ( family-family-with-dependent-descent-data-circle))
      ( eq-family-with-dependent-descent-data-circle)

  map-equiv-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    ( type-family-with-dependent-descent-data-circle x) →
    ( family-family-with-dependent-descent-data-circle
      ( base-free-loop l)
      ( map-equiv-family-with-descent-data-circle A x))
  map-equiv-family-with-dependent-descent-data-circle x =
    map-equiv (equiv-family-with-dependent-descent-data-circle x)

  coherence-square-family-with-dependent-descent-data-circle :
    ( x : type-family-with-descent-data-circle A) →
    coherence-square-maps
      ( map-equiv-family-with-dependent-descent-data-circle x)
      ( map-pseudo-aut-family-with-dependent-descent-data-circle x)
      ( tr
        ( ind-Σ (family-family-with-dependent-descent-data-circle))
        ( eq-pair-Σ
          ( loop-free-loop l)
          ( inv (coherence-square-family-with-descent-data-circle A x))))
      ( map-equiv-family-with-dependent-descent-data-circle
        ( map-aut-family-with-descent-data-circle A x))
  coherence-square-family-with-dependent-descent-data-circle =
    coherence-square-Eq-dependent-descent-data-circle
      ( descent-data-family-with-descent-data-circle A)
      ( dependent-descent-data-family-with-dependent-descent-data-circle)
      ( ev-dependent-descent-data-circle l A
        ( family-family-with-dependent-descent-data-circle))
      ( eq-family-with-dependent-descent-data-circle)

  family-for-family-with-dependent-descent-data-circle :
    family-for-dependent-descent-data-circle l A
      dependent-descent-data-family-with-dependent-descent-data-circle
  pr1 family-for-family-with-dependent-descent-data-circle =
    family-family-with-dependent-descent-data-circle
  pr2 family-for-family-with-dependent-descent-data-circle =
    eq-family-with-dependent-descent-data-circle
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

### Alternative definition of equality of descent data as homomorphisms which are equivalences

```agda
module _
  { l1 l2 : Level}
  ( P : descent-data-circle l1)
  ( Q : descent-data-circle l2)
  where

  Eq-descent-data-circle' : UU (l1 ⊔ l2)
  Eq-descent-data-circle' =
    Σ ( hom-descent-data-circle P Q)
      ( λ h → is-equiv (map-hom-descent-data-circle P Q h))

  equiv-Eq-descent-data-circle-hom-is-equiv :
    Eq-descent-data-circle P Q ≃ Eq-descent-data-circle'
  equiv-Eq-descent-data-circle-hom-is-equiv = equiv-right-swap-Σ
```

### Uniqueness of descent data characterizing a type family over the circle

Given a type `X` and an automorphism `e : X ≃ X`, there is a unique type family
`𝓓(X, e) : 𝕊¹ → U` for which `(X, e)` is descent data.

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
  ( up-circle : universal-property-circle (lsuc l2) l)
  where

  unique-family-property-universal-property-circle :
    unique-family-property-circle l2 l
  unique-family-property-universal-property-circle Q =
    is-contr-is-equiv'
      ( fiber (ev-descent-data-circle l) Q)
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

  family-for-descent-data-circle-descent-data :
    ( P : descent-data-circle l2) →
    family-for-descent-data-circle l P
  family-for-descent-data-circle-descent-data P =
    center (unique-family-property-universal-property-circle P)

  family-with-descent-data-circle-descent-data :
    ( P : descent-data-circle l2) →
    ( family-with-descent-data-circle l l2)
  pr1 (family-with-descent-data-circle-descent-data P) =
    pr1 (family-for-descent-data-circle-descent-data P)
  pr1 (pr2 (family-with-descent-data-circle-descent-data P)) = P
  pr2 (pr2 (family-with-descent-data-circle-descent-data P)) =
    pr2 (family-for-descent-data-circle-descent-data P)
```

### Characterization of the identity type of dependent descent data for the circle

```agda
module _
  { l1 l2 : Level} (P : descent-data-circle l1)
  where

  refl-Eq-dependent-descent-data-circle :
    ( Q : dependent-descent-data-circle P l2) →
    Eq-dependent-descent-data-circle P Q Q
  pr1 (refl-Eq-dependent-descent-data-circle Q) =
    id-equiv-fam (type-dependent-descent-data-circle P Q)
  pr2 (refl-Eq-dependent-descent-data-circle Q) x = refl-htpy

  Eq-eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle P l2) →
    Q ＝ T → Eq-dependent-descent-data-circle P Q T
  Eq-eq-dependent-descent-data-circle Q .Q refl =
    refl-Eq-dependent-descent-data-circle Q

  is-contr-total-Eq-dependent-descent-data-circle :
    ( Q : dependent-descent-data-circle P l2) →
    is-contr
      ( Σ ( dependent-descent-data-circle P l2)
          ( Eq-dependent-descent-data-circle P Q))
  is-contr-total-Eq-dependent-descent-data-circle Q =
    is-contr-total-Eq-structure
      ( λ R K H →
        ( x : type-descent-data-circle P) →
        coherence-square-maps
          ( map-equiv (H x))
          ( map-dependent-descent-data-circle P Q x)
          ( map-equiv (K x))
          ( map-equiv (H (map-descent-data-circle P x))))
      ( is-contr-total-equiv-fam (type-dependent-descent-data-circle P Q))
      ( type-dependent-descent-data-circle P Q ,
        id-equiv-fam (type-dependent-descent-data-circle P Q))
      ( is-contr-total-Eq-Π
        ( λ x K →
          ( map-dependent-descent-data-circle P Q x) ~
          ( map-equiv K))
        ( λ x →
          is-contr-total-htpy-equiv
            ( pseudo-aut-dependent-descent-data-circle P Q x)))

  is-equiv-Eq-eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle P l2) →
    is-equiv (Eq-eq-dependent-descent-data-circle Q T)
  is-equiv-Eq-eq-dependent-descent-data-circle Q =
    fundamental-theorem-id
      ( is-contr-total-Eq-dependent-descent-data-circle Q)
      ( Eq-eq-dependent-descent-data-circle Q)

  eq-Eq-dependent-descent-data-circle :
    ( Q T : dependent-descent-data-circle P l2) →
    Eq-dependent-descent-data-circle P Q T → Q ＝ T
  eq-Eq-dependent-descent-data-circle Q T =
    map-inv-is-equiv (is-equiv-Eq-eq-dependent-descent-data-circle Q T)
```

### Uniqueness of dependent descent data characterizing a type family over a family over the circle

Given a type family `A : 𝕊¹ → U` with corresponding descent data `(X, e)`, and a
type family `R : X → U` over `X` invariant under `e` as witnessed by `k`, there
is a unique family `B : (t : 𝕊¹) → A t → U` for which `(R, k)` is dependent
descent data over `A`.

This is so far a conjecture which remains to be shown.

```agda
module _
  { l1 l2 l3 : Level} {S : UU l1} (l : free-loop S)
  ( A : family-with-descent-data-circle l l2)
  where

  unique-dependent-family-property-circle : UU (l1 ⊔ l2 ⊔ lsuc l3)
  unique-dependent-family-property-circle =
    ( Q :
      dependent-descent-data-circle
        ( descent-data-family-with-descent-data-circle A)
        ( l3)) →
    is-contr (family-for-dependent-descent-data-circle l A Q)
```
