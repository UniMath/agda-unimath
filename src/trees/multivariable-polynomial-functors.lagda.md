# Multivariable polynomial functors

```agda
module trees.multivariable-polynomial-functors where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-homotopies
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.commuting-triangles-of-maps
open import foundation-core.retractions
open import foundation-core.torsorial-type-families
```

</details>

## Idea

{{#concept "Multivariable polynomial functors" Agda=polynomial-functor}} are a
generalization of the notion of
[polynomial endofunctors](trees.polynomial-endofunctors.md) to the case of
families of types (variables). Given a type family `A : J → Type` and a type
family `B : I → {j : J} → A j → Type` over `A`, we have a multivariable
polynomial functor `P A B`, also denoted `A ◃ B`, with action on `I`-indexed
type families given by

```text
  P A B X j := Σ (a : A j), ((i : I) → B i a → X i).
```

## Definitions

### The type of multivariable polynomial functors

```agda
polynomial-functor :
  {l1 l2 : Level} (l3 l4 : Level) →
  UU l1 → UU l2 → UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
polynomial-functor l3 l4 I J =
  Σ (J → UU l3) (λ A → (I → {j : J} → A j → UU l4))

module _
  {l1 l2 l3 l4 : Level} {I : UU l1} {J : UU l2}
  (P : polynomial-functor l3 l4 I J)
  where

  shape-polynomial-functor : J → UU l3
  shape-polynomial-functor = pr1 P

  position-polynomial-functor :
    I → {j : J} → shape-polynomial-functor j → UU l4
  position-polynomial-functor = pr2 P
```

### The action on type families of a multivariable polynomial functor

```agda
module _
  {l1 l2 l3 l4 l5 : Level} {I : UU l1} {J : UU l2}
  where

  type-polynomial-functor' :
    (A : J → UU l3) (B : I → {j : J} → A j → UU l4) →
    (I → UU l5) → (J → UU (l1 ⊔ l3 ⊔ l4 ⊔ l5))
  type-polynomial-functor' A B X j =
    Σ (A j) (λ a → (i : I) → B i a → X i)

  type-polynomial-functor :
    (P : polynomial-functor l3 l4 I J) →
    (I → UU l5) → (J → UU (l1 ⊔ l3 ⊔ l4 ⊔ l5))
  type-polynomial-functor (A , B) =
    type-polynomial-functor' A B
```

### Characterizing equality in `type-polynomial-functor`

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {I : UU l1} {J : UU l2}
  {P@(A , B) : polynomial-functor l3 l4 I J}
  {X : I → UU l5}
  where

  Eq-type-polynomial-functor :
    (x y : (j : J) → type-polynomial-functor P X j) →
    UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  Eq-type-polynomial-functor x y =
    (j : J) →
    Σ ( pr1 (x j) ＝ pr1 (y j))
      ( λ p →
        (i : I) →
        coherence-triangle-maps (pr2 (x j) i) (pr2 (y j) i) (tr (B i {j}) p))

  refl-Eq-type-polynomial-functor :
    (x : (j : J) → type-polynomial-functor P X j) →
    Eq-type-polynomial-functor x x
  refl-Eq-type-polynomial-functor x j = (refl , (λ i → refl-htpy))

  Eq-eq-type-polynomial-functor :
    (x y : (j : J) → type-polynomial-functor P X j) →
    x ＝ y → Eq-type-polynomial-functor x y
  Eq-eq-type-polynomial-functor x .x refl =
    refl-Eq-type-polynomial-functor x

  abstract
    is-torsorial-Eq-type-polynomial-functor :
      (x : (j : J) → type-polynomial-functor P X j) →
      is-torsorial (Eq-type-polynomial-functor x)
    is-torsorial-Eq-type-polynomial-functor x =
      is-torsorial-Eq-Π
        ( λ j →
          is-torsorial-Eq-structure
            { D =
              λ a y p →
              (i : I) →
              coherence-triangle-maps (pr2 (x j) i) (y i) (tr (B i {j}) p)}
            ( is-torsorial-Id (pr1 (x j)))
            ( pr1 (x j) , refl)
            ( is-torsorial-binary-htpy (pr2 (x j))))

  abstract
    is-equiv-Eq-eq-type-polynomial-functor :
      (x y : (j : J) → type-polynomial-functor P X j) →
      is-equiv (Eq-eq-type-polynomial-functor x y)
    is-equiv-Eq-eq-type-polynomial-functor x =
      fundamental-theorem-id
        ( is-torsorial-Eq-type-polynomial-functor x)
        ( Eq-eq-type-polynomial-functor x)

  eq-Eq-type-polynomial-functor :
    (x y : (j : J) → type-polynomial-functor P X j) →
    Eq-type-polynomial-functor x y → x ＝ y
  eq-Eq-type-polynomial-functor x y =
    map-inv-is-equiv (is-equiv-Eq-eq-type-polynomial-functor x y)

  is-retraction-eq-Eq-type-polynomial-functor :
    (x y : (j : J) → type-polynomial-functor P X j) →
    is-retraction
      ( Eq-eq-type-polynomial-functor x y)
      ( eq-Eq-type-polynomial-functor x y)
  is-retraction-eq-Eq-type-polynomial-functor x y =
    is-retraction-map-inv-is-equiv
      ( is-equiv-Eq-eq-type-polynomial-functor x y)

  coh-refl-eq-Eq-type-polynomial-functor :
    (x : (j : J) → type-polynomial-functor P X j) →
    ( eq-Eq-type-polynomial-functor x x
      ( refl-Eq-type-polynomial-functor x)) ＝ refl
  coh-refl-eq-Eq-type-polynomial-functor x =
    is-retraction-eq-Eq-type-polynomial-functor x x refl
```

### An action on dependent functions of multivariable polynomial functors

The following construction is not quite right for "the" action on dependent
functions, since given a type family `Y` over a type family `X`, the
construction gives only a dependent function of approximately type

```text
  (x : P X) → P (Σ B Y x)
```

rather than

```text
  (x : P X) → P (Y x).
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {I : UU l1} {J : UU l2}
  where

  dmap-Σ-polynomial-functor' :
    (A : J → UU l3) (B : I → {j : J} → A j → UU l4)
    {X : I → UU l5} {Y : (i : I) → X i → UU l6}
    (f : (i : I) (x : X i) → Y i x) →
    (x : (j : J) → type-polynomial-functor' A B X j) →
    (j : J) →
    type-polynomial-functor' A B
      ( λ i → Σ (B i (pr1 (x j))) (Y i ∘ pr2 (x j) i))
      ( j)
  dmap-Σ-polynomial-functor' A B f x j =
    ( pr1 (x j) , (λ i b → (b , f i (pr2 (x j) i b))))
```

### The action on functions of multivariable polynomial functors

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {I : UU l1} {J : UU l2}
  where

  map-polynomial-functor' :
    (A : J → UU l3) (B : I → {j : J} → A j → UU l4)
    {X : I → UU l5} {Y : I → UU l6}
    (f : (i : I) → X i → Y i) →
    (j : J) →
    type-polynomial-functor' A B X j → type-polynomial-functor' A B Y j
  map-polynomial-functor' A B f j (a , x) = (a , (λ i b → f i (x i b)))

  map-polynomial-functor :
    (P : polynomial-functor l3 l4 I J)
    {X : I → UU l5} {Y : I → UU l6}
    (f : (i : I) → X i → Y i) →
    (j : J) → type-polynomial-functor P X j → type-polynomial-functor P Y j
  map-polynomial-functor (A , B) = map-polynomial-functor' A B
```

### The action on homotopies of multivariable polynomial functors

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} {I : UU l1} {J : UU l2}
  where

  binary-htpy-polynomial-functor' :
    (A : J → UU l3) (B : I → {j : J} → A j → UU l4)
    {X : I → UU l5} {Y : I → UU l6} {f g : (i : I) → X i → Y i} →
    binary-htpy f g →
    binary-htpy (map-polynomial-functor' A B f) (map-polynomial-functor' A B g)
  binary-htpy-polynomial-functor' A B H j x =
    eq-pair-eq-fiber (eq-binary-htpy _ _ (λ i → H i ∘ pr2 x i))

  binary-htpy-polynomial-functor :
    (P : polynomial-functor l3 l4 I J)
    {X : I → UU l5} {Y : I → UU l6} {f g : (i : I) → X i → Y i} →
    binary-htpy f g →
    binary-htpy (map-polynomial-functor P f) (map-polynomial-functor P g)
  binary-htpy-polynomial-functor (A , B) = binary-htpy-polynomial-functor' A B
```

### The identity multivariable polynomial functor

```agda
module _
  {l1 : Level} {I : UU l1}
  where

  id-polynomial-functor : polynomial-functor lzero l1 I I
  id-polynomial-functor = (λ i' → unit) , (λ i {i'} * → (i' ＝ i))

  compute-type-id-polynomial-functor :
    {l2 : Level} (X : I → UU l2) (i : I) →
    type-polynomial-functor id-polynomial-functor X i ≃ X i
  compute-type-id-polynomial-functor X i =
    equivalence-reasoning
      Σ unit (λ * → (i' : I) → i ＝ i' → X i')
      ≃ ((i' : I) → i ＝ i' → X i')
        by left-unit-law-Σ (λ * → (i' : I) → i ＝ i' → X i')
      ≃ X i
        by equiv-ev-refl i

  map-compute-type-id-polynomial-functor :
    {l2 : Level} (X : I → UU l2) (i : I) →
    type-polynomial-functor id-polynomial-functor X i → X i
  map-compute-type-id-polynomial-functor X i =
    map-equiv (compute-type-id-polynomial-functor X i)

  coh-map-id-polynomial-functor :
    {l2 l3 : Level} {X : I → UU l2} {Y : I → UU l3} (f : (i : I) → X i → Y i)
    (i : I) →
    coherence-square-maps
      ( map-compute-type-id-polynomial-functor X i)
      ( map-polynomial-functor id-polynomial-functor f i)
      ( f i)
      ( map-compute-type-id-polynomial-functor Y i)
  coh-map-id-polynomial-functor f i = refl-htpy
```

### Composition of multivariable polynomial functors

Given two multivariable polynomial functors `P A B : (I → Type) → (J → Type)`
and `P C D : (J → Type) → (K → Type)`, then the composite functor
`P C D ∘ P A B` is again a polynomial functor.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {I : UU l1} {J : UU l2} {K : UU l3}
  (Q@(C , D) : polynomial-functor l6 l7 J K)
  (P@(A , B) : polynomial-functor l4 l5 I J)
  where

  shape-comp-polynomial-functor : K → UU (l2 ⊔ l4 ⊔ l6 ⊔ l7)
  shape-comp-polynomial-functor k =
    Σ (C k) (λ c → (j : J) → D j {k} c → A j)

  position-comp-polynomial-functor :
    I → {k : K} → shape-comp-polynomial-functor k → UU (l2 ⊔ l5 ⊔ l7)
  position-comp-polynomial-functor i {k} (c , a) =
    Σ J (λ j → Σ (D j {k} c) (λ d → B i {j} (a j d)))

  comp-polynomial-functor :
    polynomial-functor (l2 ⊔ l4 ⊔ l6 ⊔ l7) (l2 ⊔ l5 ⊔ l7) I K
  comp-polynomial-functor =
    ( shape-comp-polynomial-functor , position-comp-polynomial-functor)

  map-compute-type-comp-polynomial-functor :
    {l8 : Level} (X : I → UU l8) (k : K) →
    type-polynomial-functor comp-polynomial-functor X k →
    type-polynomial-functor Q (type-polynomial-functor P X) k
  map-compute-type-comp-polynomial-functor X k ((c , a) , x) =
    (c , (λ j d → (a j d , (λ i b → x i (j , d , b)))))

  map-inv-compute-type-comp-polynomial-functor :
    {l8 : Level} (X : I → UU l8) (k : K) →
    type-polynomial-functor Q (type-polynomial-functor P X) k →
    type-polynomial-functor comp-polynomial-functor X k
  map-inv-compute-type-comp-polynomial-functor X k (c , q) =
    ((c , (λ j d → pr1 (q j d))) , (λ i (j , d , b) → pr2 (q j d) i b))

  is-equiv-map-compute-type-comp-polynomial-functor :
    {l8 : Level} (X : I → UU l8) (k : K) →
    is-equiv (map-compute-type-comp-polynomial-functor X k)
  is-equiv-map-compute-type-comp-polynomial-functor X k =
    is-equiv-is-invertible
      ( map-inv-compute-type-comp-polynomial-functor X k)
      ( refl-htpy)
      ( refl-htpy)

  compute-type-comp-polynomial-functor :
    {l8 : Level} (X : I → UU l8) (k : K) →
    type-polynomial-functor comp-polynomial-functor X k ≃
    type-polynomial-functor Q (type-polynomial-functor P X) k
  compute-type-comp-polynomial-functor X k =
    ( map-compute-type-comp-polynomial-functor X k ,
      is-equiv-map-compute-type-comp-polynomial-functor X k)

  coh-map-comp-polynomial-functor :
    {l8 l9 : Level} {X : I → UU l8} {Y : I → UU l9}
    (f : (i : I) → X i → Y i) (k : K) →
    coherence-square-maps
      ( map-compute-type-comp-polynomial-functor X k)
      ( map-polynomial-functor comp-polynomial-functor f k)
      ( map-polynomial-functor Q (map-polynomial-functor P f) k)
      ( map-compute-type-comp-polynomial-functor Y k)
  coh-map-comp-polynomial-functor f k x = refl

  compute-map-comp-polynomial-functor :
    {l8 l9 : Level} {X : I → UU l8} {Y : I → UU l9}
    (f : (i : I) → X i → Y i) (k : K) →
    ( map-polynomial-functor comp-polynomial-functor f k) ~
    ( map-inv-compute-type-comp-polynomial-functor Y k ∘
      map-polynomial-functor Q (map-polynomial-functor P f) k ∘
      map-compute-type-comp-polynomial-functor X k)
  compute-map-comp-polynomial-functor f k x = refl

  compute-map-comp-polynomial-functor' :
    {l8 l9 : Level} {X : I → UU l8} {Y : I → UU l9}
    (f : (i : I) → X i → Y i) (k : K) →
    ( map-polynomial-functor Q (map-polynomial-functor P f) k) ~
    ( map-compute-type-comp-polynomial-functor Y k ∘
      map-polynomial-functor comp-polynomial-functor f k ∘
      map-inv-compute-type-comp-polynomial-functor X k)
  compute-map-comp-polynomial-functor' f k x = refl
```

## References

Multivariable polynomial functors over locally cartesian closed categories are
considered in {{#cite GK12}}.

{{#bibliography}}

## External links

- [_Multivariate containers_](https://git.app.uib.no/hott/containers/-/blob/main/src/containers/multivariate.agda)
  by [Elisabeth Stenholm](https://elisabeth.stenholm.one), Agda formalization
