# `k`-acyclic maps

```agda
module synthetic-homotopy-theory.truncated-acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.connected-maps
open import foundation.connected-types
open import foundation.constant-maps
open import foundation.dependent-epimorphisms-with-respect-to-truncated-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.dependent-products-truncated-types
open import foundation.dependent-universal-property-equivalences
open import foundation.diagonal-maps-of-types
open import foundation.embeddings
open import foundation.epimorphisms-with-respect-to-truncated-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.function-extensionality-axiom
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.functoriality-fibers-of-maps
open import foundation.homotopies
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.pullbacks
open import foundation.retracts-of-arrows
open import foundation.torsorial-type-families
open import foundation.truncated-types
open import foundation.truncation-equivalences
open import foundation.truncation-levels
open import foundation.truncations
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.truncated-acyclic-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be **`k`-acyclic** if its
[fibers](foundation-core.fibers-of-maps.md) are
[`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md).

## Definitions

### The predicate of being a `k`-acyclic map

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-truncated-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-truncated-acyclic-map-Prop f =
    Π-Prop B (λ b → is-truncated-acyclic-Prop k (fiber f b))

  is-truncated-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-truncated-acyclic-map f = type-Prop (is-truncated-acyclic-map-Prop f)

  is-prop-is-truncated-acyclic-map :
    (f : A → B) → is-prop (is-truncated-acyclic-map f)
  is-prop-is-truncated-acyclic-map f =
    is-prop-type-Prop (is-truncated-acyclic-map-Prop f)
```

## Properties

### A map is `k`-acyclic if and only if it is an epimorphism with respect to `k`-types

This theorem characterizes the
[`k`-epimorphisms](foundation.epimorphisms-with-respect-to-truncated-types.md)
in homotopy type theory. {{#cite BdJR24}}

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-epimorphism-Truncated-Type e b =
    is-connected-equiv
      ( equiv-fiber-codiagonal-map-suspension-fiber f b)
      ( is-connected-codiagonal-map-is-epimorphism-Truncated-Type k f e b)

  is-epimorphism-is-truncated-acyclic-map-Truncated-Type :
    is-truncated-acyclic-map k f → is-epimorphism-Truncated-Type k f
  is-epimorphism-is-truncated-acyclic-map-Truncated-Type ac =
    is-epimorphism-is-connected-codiagonal-map-Truncated-Type k f
      ( λ b →
        is-connected-equiv'
          ( equiv-fiber-codiagonal-map-suspension-fiber f b)
          ( ac b))
```

### A type is `k`-acyclic if and only if its terminal map is a `k`-acyclic map

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-map-terminal-map-is-truncated-acyclic :
    is-truncated-acyclic k A →
    is-truncated-acyclic-map k (terminal-map A)
  is-truncated-acyclic-map-terminal-map-is-truncated-acyclic ac u =
    is-truncated-acyclic-equiv (equiv-fiber-terminal-map u) ac

  is-truncated-acyclic-is-truncated-acyclic-map-terminal-map :
    is-truncated-acyclic-map k (terminal-map A) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-truncated-acyclic-map-terminal-map ac =
    is-truncated-acyclic-equiv inv-equiv-fiber-terminal-map-star (ac star)
```

### A type is `k`-acyclic if and only if the constant map from any `k`-type is an embedding

More precisely, `A` is `k`-acyclic if and only if for all `k`-types `X`, the map

```text
  Δ : X → (A → X)
```

is an embedding.

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Type :
    is-truncated-acyclic k A →
    {l' : Level} (X : Truncated-Type l' k) →
    is-emb (diagonal-exponential (type-Truncated-Type X) A)
  is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Type ac X =
    is-emb-comp
      ( precomp (terminal-map A) (type-Truncated-Type X))
      ( map-inv-left-unit-law-function-type (type-Truncated-Type X))
      ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type
        ( terminal-map A)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac)
        ( X))
      ( is-emb-is-equiv
        ( is-equiv-map-inv-left-unit-law-function-type (type-Truncated-Type X)))

  is-truncated-acyclic-is-emb-diagonal-exponential-Truncated-Type :
    ({l' : Level} (X : Truncated-Type l' k) →
    is-emb (diagonal-exponential (type-Truncated-Type X) A)) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-emb-diagonal-exponential-Truncated-Type e =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
      ( is-truncated-acyclic-map-is-epimorphism-Truncated-Type
        ( terminal-map A)
        ( λ X →
          is-emb-triangle-is-equiv'
            ( diagonal-exponential (type-Truncated-Type X) A)
            ( precomp (terminal-map A) (type-Truncated-Type X))
            ( map-inv-left-unit-law-function-type (type-Truncated-Type X))
            ( refl-htpy)
            ( is-equiv-map-inv-left-unit-law-function-type
              ( type-Truncated-Type X))
            ( e X)))
```

### A type is `k`-acyclic if and only if the constant map from any identity type of any `k`-type is an equivalence

More precisely, `A` is `k`-acyclic if and only if for all `k`-types `X` and
elements `x,y : X`, the map

```text
  Δ : (x ＝ y) → (A → x ＝ y)
```

is an equivalence.

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Type :
    is-truncated-acyclic k A →
    {l' : Level} (X : Truncated-Type l' k) (x y : type-Truncated-Type X) →
    is-equiv (diagonal-exponential (x ＝ y) A)
  is-equiv-diagonal-exponential-Id-is-acyclic-Truncated-Type ac X x y =
    is-equiv-htpy
      ( htpy-eq ∘ ap (diagonal-exponential (type-Truncated-Type X) A) {x} {y})
      ( htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Id x y A)
      ( is-equiv-comp
        ( htpy-eq)
        ( ap (diagonal-exponential (type-Truncated-Type X) A))
        ( is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Type
          ( A)
          ( ac)
          ( X)
          ( x)
          ( y))
        ( funext
          ( diagonal-exponential (type-Truncated-Type X) A x)
          ( diagonal-exponential (type-Truncated-Type X) A y)))

  is-truncated-acyclic-is-equiv-diagonal-exponential-Id-Truncated-Type :
    ( {l' : Level} (X : Truncated-Type l' k) (x y : type-Truncated-Type X) →
      is-equiv (diagonal-exponential (x ＝ y) A)) →
    is-truncated-acyclic k A
  is-truncated-acyclic-is-equiv-diagonal-exponential-Id-Truncated-Type h =
    is-truncated-acyclic-is-emb-diagonal-exponential-Truncated-Type A
      ( λ X x y →
        is-equiv-right-factor
          ( htpy-eq)
          ( ap (diagonal-exponential (type-Truncated-Type X) A))
          ( funext
            ( diagonal-exponential (type-Truncated-Type X) A x)
            ( diagonal-exponential (type-Truncated-Type X) A y))
          ( is-equiv-htpy
            ( diagonal-exponential (x ＝ y) A)
            ( htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eq
              ( x)
              ( y)
              ( A))
            ( h X x y)))
```

### A map is `k`-acyclic if and only if it is a dependent `k`-epimorphism { #a-map-is-k-acyclic-if-and-only-if-it-is-an-dependent-k-epimorphism }

<!-- The explicit id is there because it's linked to from the BdJR24 paper -->

The proof is similar to that of dependent epimorphisms and
[acyclic-maps](synthetic-homotopy-theory.acyclic-maps.md).

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Type :
    is-dependent-epimorphism-Truncated-Type k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-dependent-epimorphism-Truncated-Type e =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type f
      ( is-epimorphism-is-dependent-epimorphism-Truncated-Type f e)

  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type :
    is-truncated-acyclic-map k f → is-dependent-epimorphism-Truncated-Type k f
  is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type ac C =
    is-emb-comp
      ( ( precomp-Π
          ( map-inv-equiv-total-fiber f)
          ( type-Truncated-Type ∘ C ∘ pr1)) ∘
        ( ind-Σ))
      ( map-Π
        ( λ b → diagonal-exponential (type-Truncated-Type (C b)) (fiber f b)))
      ( is-emb-comp
        ( precomp-Π
          ( map-inv-equiv-total-fiber f)
          ( type-Truncated-Type ∘ C ∘ pr1))
        ( ind-Σ)
        ( is-emb-is-equiv
          ( is-equiv-precomp-Π-is-equiv
            ( is-equiv-map-inv-equiv-total-fiber f)
              (type-Truncated-Type ∘ C ∘ pr1)))
        ( is-emb-is-equiv is-equiv-ind-Σ))
      ( is-emb-map-Π
        ( λ b →
          is-emb-diagonal-exponential-is-truncated-acyclic-Truncated-Type
            ( fiber f b)
            ( ac b)
            ( C b)))
```

In particular, every `k`-epimorphism is actually a dependent `k`-epimorphism.

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-dependent-epimorphism-is-epimorphism-Truncated-Type :
    is-epimorphism-Truncated-Type k f →
    is-dependent-epimorphism-Truncated-Type k f
  is-dependent-epimorphism-is-epimorphism-Truncated-Type e =
    is-dependent-epimorphism-is-truncated-acyclic-map-Truncated-Type f
      ( is-truncated-acyclic-map-is-epimorphism-Truncated-Type f e)
```

### The class of `k`-acyclic maps is closed under composition and has the right cancellation property

Since the `k`-acyclic maps are precisely the `k`-epimorphisms this follows from
the corresponding facts about
[`k`-epimorphisms](foundation.epimorphisms-with-respect-to-truncated-types.md).

```agda
module _
  {l1 l2 l3 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-truncated-acyclic-map-comp :
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (g ∘ f)
  is-truncated-acyclic-map-comp ag af =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type (g ∘ f)
      ( is-epimorphism-comp-Truncated-Type k g f
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type g ag)
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type f af))

  is-truncated-acyclic-map-left-factor :
    is-truncated-acyclic-map k (g ∘ f) →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k g
  is-truncated-acyclic-map-left-factor ac af =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type g
      ( is-epimorphism-left-factor-Truncated-Type k g f
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type (g ∘ f) ac)
        ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type f af))
```

### Every `k`-connected map is `(k+1)`-acyclic

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-succ-is-connected-map :
    is-connected-map k f → is-truncated-acyclic-map (succ-𝕋 k) f
  is-truncated-acyclic-map-succ-is-connected-map c b =
    is-truncated-acyclic-succ-is-connected (c b)
```

In particular, the unit of the `k`-truncation is `(k+1)`-acyclic

```agda
is-truncated-acyclic-map-succ-unit-trunc :
  {l : Level} {k : 𝕋} (A : UU l) →
  is-truncated-acyclic-map (succ-𝕋 k) (unit-trunc {A = A})
is-truncated-acyclic-map-succ-unit-trunc {k = k} A =
  is-truncated-acyclic-map-succ-is-connected-map
    ( unit-trunc)
    ( is-connected-map-unit-trunc k)
```

### A type is `(k+1)`-acyclic if and only if its `k`-truncation is

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-succ-is-truncated-acyclic-succ-type-trunc :
    is-truncated-acyclic (succ-𝕋 k) (type-trunc k A) →
    is-truncated-acyclic (succ-𝕋 k) A
  is-truncated-acyclic-succ-is-truncated-acyclic-succ-type-trunc ac =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
      ( is-truncated-acyclic-map-comp
        ( terminal-map (type-trunc k A))
        ( unit-trunc)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic
          ( type-trunc k A)
          ( ac))
        ( is-truncated-acyclic-map-succ-unit-trunc A))

  is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succ :
    is-truncated-acyclic (succ-𝕋 k) A →
    is-truncated-acyclic (succ-𝕋 k) (type-trunc k A)
  is-truncated-acyclic-succ-type-trunc-is-truncated-acyclic-succ ac =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map
      ( type-trunc k A)
      ( is-truncated-acyclic-map-left-factor
        ( terminal-map (type-trunc k A))
        ( unit-trunc)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac)
        ( is-truncated-acyclic-map-succ-unit-trunc A))
```

### Every `k`-equivalence is `k`-acyclic

```agda
module _
  {l1 l2 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-truncated-acyclic-map-is-truncation-equivalence :
    is-truncation-equivalence k f → is-truncated-acyclic-map k f
  is-truncated-acyclic-map-is-truncation-equivalence e =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type f
      ( λ C → is-emb-is-equiv (is-equiv-precomp-is-truncation-equivalence e C))
```

### `k`-acyclic maps are closed under pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-truncated-acyclic-map-vertical-map-cone-is-pullback :
    is-pullback f g c →
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k (vertical-map-cone f g c)
  is-truncated-acyclic-map-vertical-map-cone-is-pullback pb ac a =
    is-truncated-acyclic-equiv
      ( map-fiber-vertical-map-cone f g c a ,
        is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback f g c pb a)
      ( ac (f a))

module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-truncated-acyclic-map-horizontal-map-cone-is-pullback :
    is-pullback f g c →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (horizontal-map-cone f g c)
  is-truncated-acyclic-map-horizontal-map-cone-is-pullback pb =
    is-truncated-acyclic-map-vertical-map-cone-is-pullback g f
      ( swap-cone f g c)
      ( is-pullback-swap-cone f g c pb)
```

### `k`-acyclic types are closed under dependent pair types

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : A → UU l2)
  where

  is-truncated-acyclic-Σ :
    is-truncated-acyclic k A →
    ((a : A) → is-truncated-acyclic k (B a)) →
    is-truncated-acyclic k (Σ A B)
  is-truncated-acyclic-Σ ac-A ac-B =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map
      ( Σ A B)
      ( is-truncated-acyclic-map-comp
        ( terminal-map A)
        ( pr1)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac-A)
        ( λ a → is-truncated-acyclic-equiv (equiv-fiber-pr1 B a) (ac-B a)))
```

### `k`-acyclic types are closed under binary products

```agda
module _
  {l1 l2 : Level} {k : 𝕋} (A : UU l1) (B : UU l2)
  where

  is-truncated-acyclic-product :
    is-truncated-acyclic k A →
    is-truncated-acyclic k B →
    is-truncated-acyclic k (A × B)
  is-truncated-acyclic-product ac-A ac-B =
    is-truncated-acyclic-is-truncated-acyclic-map-terminal-map
      ( A × B)
      ( is-truncated-acyclic-map-comp
        ( terminal-map B)
        ( pr2)
        ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic B ac-B)
        ( is-truncated-acyclic-map-horizontal-map-cone-is-pullback
          ( terminal-map A)
          ( terminal-map B)
          ( cone-cartesian-product A B)
          ( is-pullback-cartesian-product A B)
          ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic A ac-A)))
```

### Inhabited, locally `k`-acyclic types are `k`-acyclic

```agda
module _
  {l : Level} {k : 𝕋} (A : UU l)
  where

  is-truncated-acyclic-inhabited-is-truncated-acyclic-Id :
    is-inhabited A →
    ((a b : A) → is-truncated-acyclic k (a ＝ b)) →
    is-truncated-acyclic k A
  is-truncated-acyclic-inhabited-is-truncated-acyclic-Id h l-ac =
    apply-universal-property-trunc-Prop h
      ( is-truncated-acyclic-Prop k A)
      ( λ a →
        is-truncated-acyclic-is-truncated-acyclic-map-terminal-map A
          ( is-truncated-acyclic-map-left-factor
            ( terminal-map A)
            ( point a)
            ( is-truncated-acyclic-map-terminal-map-is-truncated-acyclic
              ( unit)
              ( is-truncated-acyclic-unit))
            ( λ b →
              is-truncated-acyclic-equiv
                ( compute-fiber-point a b)
                ( l-ac a b))))
```

### `k`-acyclic maps are closed under retracts

```agda
module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-truncated-acyclic-map-retract-of :
    f retract-of-arrow g →
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k f
  is-truncated-acyclic-map-retract-of R ac b =
    is-truncated-acyclic-retract-of
      ( retract-fiber-retract-arrow f g R b)
      ( ac (map-codomain-inclusion-retract-arrow f g R b))
```

### `k`-acyclic maps are closed under pushouts

**Proof:** We consider the pushout squares

```text
        g          j
   S -------> B -------> C
   |          |          |
 f |          | j        | inr
   ∨        ⌜ ∨        ⌜ ∨
   A -------> C -------> ∙
        i          inl
```

We assume that `f` is `k`-acyclic and we want to prove that `j` is too. For
this, it suffices to show that for any `k`-type `X`, the second projection
`cocone j j X → (C → X)` is an equivalence, as shown in the file on
[epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md).

For this, we use the following commutative diagram

```text
                      ≃
   (∙ → X) ------------------------> cocone f (j ∘ g) X
      |      (by pushout pasting)            |
      |                                      |
    ≃ | (universal                           | vertical-map-cocone
      |  property)                           | (second projection)
      ∨                                      ∨
 cocone j j X --------------------------> (C → X)
                 vertical-map-cocone
                 (second projection)
```

where we first show the right map to be an equivalence using that `f` is
`k`-acyclic.

As for [acyclic maps](synthetic-homotopy-theory.acyclic-maps.md), we use the
following equivalences for that purpose:

```text
          cocone-map f (j ∘ g)
 (C → X) -----------------------> cocone f (j ∘ g) X
                               ̇= Σ (l : A → X) ,
                                 Σ (r : C → X) , l ∘ f ~ r ∘ j ∘ g
       (using the left square)
                               ≃ Σ (l : A → X) ,
                                 Σ (r : C → X) , l ∘ f ~ r ∘ i ∘ f
 (since f is `k`-acyclic/epic)
                               ≃ Σ (l : A → X) , Σ (r : C → X) , l ~ r ∘ i
                               ≃ Σ (r : C → X) , Σ (l : A → X) , l ~ r ∘ i
        (contracting at r ∘ i)
                               ≃ (C → X)
```

```agda
module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  equiv-cocone-postcomp-vertical-map-cocone-Truncated-Type :
    is-truncated-acyclic-map k f →
    {l5 : Level} (X : Truncated-Type l5 k) →
    cocone f (vertical-map-cocone f g c ∘ g) (type-Truncated-Type X) ≃
    (C → type-Truncated-Type X)
  equiv-cocone-postcomp-vertical-map-cocone-Truncated-Type ac X =
    equivalence-reasoning
        cocone f (vertical-map-cocone f g c ∘ g) (type-Truncated-Type X)
      ≃ cocone f (horizontal-map-cocone f g c ∘ f) (type-Truncated-Type X)
        by
          equiv-tot
          ( λ u →
            equiv-tot
              ( λ v →
                equiv-concat-htpy'
                  ( u ∘ f)
                  ( λ s → ap v (inv-htpy (coherence-square-cocone f g c) s))))
      ≃ Σ ( A → type-Truncated-Type X)
          ( λ u →
            Σ ( C → type-Truncated-Type X)
              ( λ v → u ∘ f ＝ v ∘ horizontal-map-cocone f g c ∘ f))
        by equiv-tot ( λ u → equiv-tot ( λ v → equiv-eq-htpy))
      ≃ Σ ( A → type-Truncated-Type X)
          ( λ u →
            Σ ( C → type-Truncated-Type X)
              ( λ v → u ＝ v ∘ horizontal-map-cocone f g c))
        by
          equiv-tot
          ( λ u →
            equiv-tot
              ( λ v →
                inv-equiv-ap-is-emb
                  ( is-epimorphism-is-truncated-acyclic-map-Truncated-Type
                    ( f)
                    ( ac)
                    ( X))))
      ≃ Σ ( C → type-Truncated-Type X)
          ( λ v →
            Σ ( A → type-Truncated-Type X)
              ( λ u → u ＝ v ∘ horizontal-map-cocone f g c))
        by
          equiv-left-swap-Σ
      ≃ (C → type-Truncated-Type X)
        by
          equiv-pr1 (λ v → is-torsorial-Id' (v ∘ horizontal-map-cocone f g c))

  is-truncated-acyclic-map-vertical-map-cocone-is-pushout :
    is-pushout f g c →
    is-truncated-acyclic-map k f →
    is-truncated-acyclic-map k (vertical-map-cocone f g c)
  is-truncated-acyclic-map-vertical-map-cocone-is-pushout po ac =
    is-truncated-acyclic-map-is-epimorphism-Truncated-Type
      ( vertical-map-cocone f g c)
      ( is-epimorphism-is-equiv-vertical-map-cocone-Truncated-Type k
        ( vertical-map-cocone f g c)
        ( λ X →
          is-equiv-bottom-is-equiv-top-square
            ( cocone-map
              ( vertical-map-cocone f g c)
              ( vertical-map-cocone f g c)
              ( cocone-pushout
                ( vertical-map-cocone f g c)
                ( vertical-map-cocone f g c)))
            ( map-equiv
              ( equiv-cocone-postcomp-vertical-map-cocone-Truncated-Type ac X))
            ( cocone-map f
              ( vertical-map-cocone f g c ∘ g)
              ( cocone-comp-horizontal f g
                ( vertical-map-cocone f g c)
                ( c)
                ( cocone-pushout
                  ( vertical-map-cocone f g c)
                  ( vertical-map-cocone f g c))))
            ( vertical-map-cocone
              ( vertical-map-cocone f g c)
              ( vertical-map-cocone f g c))
            ( refl-htpy)
            ( up-pushout
              ( vertical-map-cocone f g c)
              ( vertical-map-cocone f g c)
              ( type-Truncated-Type X))
            ( is-equiv-map-equiv
              ( equiv-cocone-postcomp-vertical-map-cocone-Truncated-Type ac X))
            ( universal-property-pushout-rectangle-universal-property-pushout-right
              ( f)
              ( g)
              ( vertical-map-cocone f g c)
              ( c)
              ( cocone-pushout
                ( vertical-map-cocone f g c)
                ( vertical-map-cocone f g c))
              ( universal-property-pushout-is-pushout f g c po)
              ( up-pushout
                ( vertical-map-cocone f g c)
                ( vertical-map-cocone f g c))
              ( type-Truncated-Type X))))

module _
  {l1 l2 l3 l4 : Level} {k : 𝕋} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  is-truncated-acyclic-map-horizontal-map-cocone-is-pushout :
    is-pushout f g c →
    is-truncated-acyclic-map k g →
    is-truncated-acyclic-map k (horizontal-map-cocone f g c)
  is-truncated-acyclic-map-horizontal-map-cocone-is-pushout po =
    is-truncated-acyclic-map-vertical-map-cocone-is-pushout g f
      ( swap-cocone f g C c)
      ( is-pushout-swap-cocone-is-pushout f g C c po)
```

## See also

- [Acyclic maps](synthetic-homotopy-theory.acyclic-maps.md)
- [Acyclic types](synthetic-homotopy-theory.acyclic-types.md)
- [`k`-acyclic types](synthetic-homotopy-theory.truncated-acyclic-types.md)
- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)
