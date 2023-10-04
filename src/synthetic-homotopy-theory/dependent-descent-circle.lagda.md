# Dependent descent for the circle

```agda
module synthetic-homotopy-theory.dependent-descent-circle where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.descent-circle
open import synthetic-homotopy-theory.free-loops
```

</details>

## Idea

The **dependent descent property of the circle** asserts that a family over a
family `P` over the circle is equivalently described by **dependent descent
data** over the descent data of `P`, which is defined as a
[dependent type with an automorphism](structured-types.dependent-types-equipped-with-automorphisms.md)

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
