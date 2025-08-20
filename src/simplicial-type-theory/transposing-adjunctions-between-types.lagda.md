# Transposing adjunctions between types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.transposing-adjunctions-between-types
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-identifications
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.postcomposition-functions
open import foundation.precomposition-functions
open import foundation.univalence
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-identifications-concatenation

open import foundation-core.equivalences
open import foundation-core.homotopies

open import simplicial-type-theory.dependent-directed-edges I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-edges-dependent-pair-types I
open import simplicial-type-theory.fully-faithful-maps I
open import simplicial-type-theory.natural-transformations I
```

</details>

## Idea

Consider a pair of mutually converse maps `L : A ↔ B : R`. We say that `L` and
`R` form a
{{#concept "transposing adjunction" Disambiguation=between types in simplicial type theory"}}
if we have a binary family of [equivalences](foundation-core.equivalences.md)

```text
  (x : A) (y : B) → hom▵ B (L x) y ≃ hom▵ A x (R y).
```

## Definitions

### Transposing adjoint pairs

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-adjunction : (A → B) → (B → A) → UU (I1 ⊔ l1 ⊔ l2)
  is-transposing-adjunction L R = (x : A) (y : B) → hom▵ (L x) y ≃ hom▵ x (R y)
```

### Transposing left adjoints

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-left-adjoint : (A → B) → UU (I1 ⊔ l1 ⊔ l2)
  is-transposing-left-adjoint L = Σ (B → A) (is-transposing-adjunction L)
```

### Transposing right adjoints

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-right-adjoint : (A → B) → UU (I1 ⊔ l1 ⊔ l2)
  is-transposing-right-adjoint R =
    Σ (B → A) (λ L → is-transposing-adjunction L R)
```

### Transposing adjunctions

```agda
transposing-adjunction : {l1 l2 : Level} → UU l1 → UU l2 → UU (I1 ⊔ l1 ⊔ l2)
transposing-adjunction A B = Σ (A → B) is-transposing-left-adjoint

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (H : transposing-adjunction A B)
  where

  map-left-adjoint-transposing-adjunction : A → B
  map-left-adjoint-transposing-adjunction = pr1 H

  is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction :
    is-transposing-left-adjoint map-left-adjoint-transposing-adjunction
  is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction = pr2 H

  map-right-adjoint-transposing-adjunction : B → A
  map-right-adjoint-transposing-adjunction =
    pr1 is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction

  is-transposing-adjunction-transposing-adjunction :
    is-transposing-adjunction
      map-left-adjoint-transposing-adjunction
      map-right-adjoint-transposing-adjunction
  is-transposing-adjunction-transposing-adjunction =
    pr2 is-transposing-left-adjoint-map-left-adjoint-transposing-adjunction

  is-transposing-right-adjoint-map-right-adjoint-transposing-adjunction :
    is-transposing-right-adjoint map-right-adjoint-transposing-adjunction
  is-transposing-right-adjoint-map-right-adjoint-transposing-adjunction =
    ( map-left-adjoint-transposing-adjunction ,
      is-transposing-adjunction-transposing-adjunction)
```

### The unit and counit natural transformations associated to a transposing adjunction

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  unit-is-transposing-adjunction :
    {L : A → B} {R : B → A} →
    is-transposing-adjunction L R → (id ⇒▵ R ∘ L)
  unit-is-transposing-adjunction {L} {R} H x =
    map-equiv (H x (L x)) (id-hom▵ (L x))

  counit-is-transposing-adjunction :
    {L : A → B} {R : B → A} →
    is-transposing-adjunction L R → (L ∘ R ⇒▵ id)
  counit-is-transposing-adjunction {L} {R} H y =
    map-inv-equiv (H (R y) y) (id-hom▵ (R y))
```

## Properties

### The identity function is a transposing adjunction

```agda
module _
  {l : Level} {A : UU l}
  where

  is-transposing-adjunction-id : is-transposing-adjunction (id {A = A}) id
  is-transposing-adjunction-id x y = id-equiv

  is-transposing-adjoint-id : is-transposing-left-adjoint (id {A = A})
  is-transposing-adjoint-id = id , is-transposing-adjunction-id

  is-transposing-adjoint-id' : is-transposing-right-adjoint (id {A = A})
  is-transposing-adjoint-id' = id , is-transposing-adjunction-id

  id-transposing-adjunction : transposing-adjunction A A
  id-transposing-adjunction = (id , id , is-transposing-adjunction-id)
```

### Equivalences are transposing adjunctions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (u : is-equiv f)
  where

  is-transposing-adjunction-is-equiv' :
    is-transposing-adjunction (map-inv-is-equiv u) f
  is-transposing-adjunction-is-equiv' y x =
    equiv-eq (ap (λ p → hom▵ p (f x)) (is-section-map-inv-is-equiv u y)) ∘e
    equiv-action-hom▵ (f , u) (map-inv-is-equiv u y) x

  is-transposing-adjunction-is-equiv :
    is-transposing-adjunction f (map-inv-is-equiv u)
  is-transposing-adjunction-is-equiv x y =
    inv-equiv
      ( equiv-eq (ap (hom▵ (f x)) (is-section-map-inv-is-equiv u y)) ∘e
        equiv-action-hom▵ (f , u) x (map-inv-is-equiv u y))

  is-transposing-left-adjoint-is-equiv : is-transposing-left-adjoint f
  is-transposing-left-adjoint-is-equiv =
    (map-inv-is-equiv u , is-transposing-adjunction-is-equiv)

  is-transposing-right-adjoint-is-equiv : is-transposing-right-adjoint f
  is-transposing-right-adjoint-is-equiv =
    (map-inv-is-equiv u , is-transposing-adjunction-is-equiv')
```

### Composition of transposing adjunctions

Given a diagram of transposing adjunctions

```text
       R         R'
    <----->   -------
  A    ⊤    B    ⊤    C
    ------>   ------>
       L         L',
```

then we have a composite transposing adjunction `L' ∘ L ⊣ R ∘ R'`.

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  is-transposing-adjunction-comp :
    {L : A → B} {L' : B → C} {R : B → A} {R' : C → B} →
    is-transposing-adjunction L' R' →
    is-transposing-adjunction L R →
    is-transposing-adjunction (L' ∘ L) (R ∘ R')
  is-transposing-adjunction-comp {L} {L'} {R} {R'} H H' x y =
    H' x (R' y) ∘e H (L x) y

  is-transposing-left-adjoint-comp :
    {L : A → B} {L' : B → C} →
    is-transposing-left-adjoint L' →
    is-transposing-left-adjoint L →
    is-transposing-left-adjoint (L' ∘ L)
  is-transposing-left-adjoint-comp (R' , H') (R , H) =
    ( R ∘ R' , is-transposing-adjunction-comp H' H)

  is-transposing-right-adjoint-comp :
    {R : B → A} {R' : C → B} →
    is-transposing-right-adjoint R →
    is-transposing-right-adjoint R' →
    is-transposing-right-adjoint (R ∘ R')
  is-transposing-right-adjoint-comp (L' , H') (L , H) =
    ( L ∘ L' , is-transposing-adjunction-comp H H')

  comp-transposing-adjunction :
    transposing-adjunction B C →
    transposing-adjunction A B →
    transposing-adjunction A C
  comp-transposing-adjunction (L' , R' , H') (L , R , H) =
    ( L' ∘ L , R ∘ R' , is-transposing-adjunction-comp H' H)
```

### Dependent products of transposing adjunctions

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {A : I → UU l2} {B : I → UU l3}
  where

  is-transposing-adjunction-Π :
    {L : (x : I) → A x → B x} {R : (x : I) → B x → A x} →
    ((x : I) → is-transposing-adjunction (L x) (R x)) →
    is-transposing-adjunction (map-Π L) (map-Π R)
  is-transposing-adjunction-Π H f g =
    inv-equiv extensionality-natural-transformation▵ ∘e
    equiv-Π-equiv-family (λ i → H i (f i) (g i)) ∘e
    extensionality-natural-transformation▵

  is-transposing-left-adjoint-Π :
    {L : (x : I) → A x → B x} →
    ((x : I) → is-transposing-left-adjoint (L x)) →
    is-transposing-left-adjoint (map-Π L)
  is-transposing-left-adjoint-Π H =
    ( map-Π (pr1 ∘ H) , is-transposing-adjunction-Π (pr2 ∘ H))

  is-transposing-right-adjoint-Π :
    {R : (x : I) → B x → A x} →
    ((x : I) → is-transposing-right-adjoint (R x)) →
    is-transposing-right-adjoint (map-Π R)
  is-transposing-right-adjoint-Π H =
    ( map-Π (pr1 ∘ H) , is-transposing-adjunction-Π (pr2 ∘ H))

  transposing-adjunction-Π :
    ((x : I) → transposing-adjunction (A x) (B x)) →
    transposing-adjunction ((x : I) → A x) ((x : I) → B x)
  transposing-adjunction-Π H =
    ( map-Π (map-left-adjoint-transposing-adjunction ∘ H) ,
      map-Π (map-right-adjoint-transposing-adjunction ∘ H) ,
      is-transposing-adjunction-Π
        ( is-transposing-adjunction-transposing-adjunction ∘ H))
```

This is proven for families of one-sided inverse adjunctions between Rezk types
in Appendix B of {{#cite BW23}}.

### Postcomposition by transposing adjunctions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-transposing-adjunction-postcomp :
    {l : Level} (X : UU l) {L : A → B} {R : B → A} →
    is-transposing-adjunction L R →
    is-transposing-adjunction (postcomp X L) (postcomp X R)
  is-transposing-adjunction-postcomp X H = is-transposing-adjunction-Π (λ _ → H)

  transposing-adjunction-postcomp :
    {l : Level} (X : UU l) →
    transposing-adjunction A B →
    transposing-adjunction (X → A) (X → B)
  transposing-adjunction-postcomp X H = transposing-adjunction-Π (λ _ → H)
```

### Base change of transposing adjunctions

Given a transposing right adjoint `R : A → B`, `L ⊣ R` and a map `j : B' → B`
such that `R ∘ L ∘ j ~ j`, then the base change of `R` along `j`, `R'`, has a
left adjoint right inverse.

**Proof.** Given a homotopy `H : R ∘ L ∘ j ~ j` we obtain the cone

```text
     L ∘ j
  B' -----> A
  ║         |
  ║    H    | R
  ║         ∨
  B' -----> B
       j
```

which, by the universal property of base change gives us a right inverse `L'` to
`R' : A' → B'`. Now...

> This remains to be formalized

### Retracts of transposing adjunctions

Maps that are retracts of transposing adjoints are transposing adjoints
themselves.

**Proof.** Given a retract of maps

```text
          i            r
    A' --------> A --------> A'
    |           | ∧          |
  R'|         R |⊢| L        |R'
    ∨           ∨ |          ∨
    B' --------> B --------> B'
           j           k
```

then the functorial action of functions on directed edges gives us a binary
family of retracts

```text
  hom A' x y ---> hom A (i x) (i y) ---> hom A' x y
```

We of course get a canonical map `L' : B' → A'` defined by the above retract of
maps. Now, we have a chain of maps

```text
    hom A' (L' x) y
  → hom A (i (L' x)) (i y)
  = hom B (j x) (R (i y))
  = hom B (j x) (j (R' y))
  → hom B' (k (j x)) (k (j (R' y)))
  = hom B' x (R' y)
```

and by our initial retract this total composite is an equivalence. Hence `L'` is
a transposing adjoint to `R'`. □

> This remains to be formalized.

## References

{{#bibliography}}
