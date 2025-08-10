# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.cones-over-cospan-diagrams
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-epimorphisms
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.diagonal-maps-of-types
open import foundation.embeddings
open import foundation.epimorphisms
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
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
open import foundation.retracts-of-maps
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-cartesian-product-types
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types
open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

A map `f : A → B` is said to be **acyclic** if its
[fibers](foundation-core.fibers-of-maps.md) are
[acyclic types](synthetic-homotopy-theory.acyclic-types.md).

## Definitions

### The predicate of being an acyclic map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-acyclic-map-Prop : (A → B) → Prop (l1 ⊔ l2)
  is-acyclic-map-Prop f = Π-Prop B (λ b → is-acyclic-Prop (fiber f b))

  is-acyclic-map : (A → B) → UU (l1 ⊔ l2)
  is-acyclic-map f = type-Prop (is-acyclic-map-Prop f)

  is-prop-is-acyclic-map : (f : A → B) → is-prop (is-acyclic-map f)
  is-prop-is-acyclic-map f = is-prop-type-Prop (is-acyclic-map-Prop f)
```

## Properties

### A map is acyclic if and only if it is an epimorphism

This theorem characterizes the usual [epimorphisms](foundation.epimorphisms.md)
in homotopy type theory. {{#cite BdJR24}}

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-acyclic-map-is-epimorphism : is-epimorphism f → is-acyclic-map f
  is-acyclic-map-is-epimorphism e b =
    is-contr-equiv
      ( fiber (codiagonal-map f) b)
      ( equiv-fiber-codiagonal-map-suspension-fiber f b)
      ( is-contr-map-is-equiv
        ( is-equiv-codiagonal-map-is-epimorphism f e)
        ( b))

  is-epimorphism-is-acyclic-map : is-acyclic-map f → is-epimorphism f
  is-epimorphism-is-acyclic-map ac =
    is-epimorphism-is-equiv-codiagonal-map f
      ( is-equiv-is-contr-map
        ( λ b →
          is-contr-equiv
            ( suspension (fiber f b))
            ( inv-equiv (equiv-fiber-codiagonal-map-suspension-fiber f b))
            ( ac b)))
```

### A type is acyclic if and only if its terminal map is an acyclic map

```agda
module _
  {l : Level} (A : UU l)
  where

  is-acyclic-map-terminal-map-is-acyclic :
    is-acyclic A → is-acyclic-map (terminal-map A)
  is-acyclic-map-terminal-map-is-acyclic ac u =
    is-acyclic-equiv (equiv-fiber-terminal-map u) ac

  is-acyclic-is-acyclic-map-terminal-map :
    is-acyclic-map (terminal-map A) → is-acyclic A
  is-acyclic-is-acyclic-map-terminal-map ac =
    is-acyclic-equiv inv-equiv-fiber-terminal-map-star (ac star)
```

### A type is acyclic if and only if the constant map from any type is an embedding

More precisely, `A` is acyclic if and only if for all types `X`, the map

```text
  Δ : X → (A → X)
```

is an embedding.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-emb-diagonal-exponential-is-acyclic :
    is-acyclic A →
    {l' : Level} (X : UU l') → is-emb (diagonal-exponential X A)
  is-emb-diagonal-exponential-is-acyclic ac X =
    is-emb-comp
      ( precomp (terminal-map A) X)
      ( map-inv-left-unit-law-function-type X)
      ( is-epimorphism-is-acyclic-map (terminal-map A)
        ( is-acyclic-map-terminal-map-is-acyclic A ac)
        ( X))
      ( is-emb-is-equiv (is-equiv-map-inv-left-unit-law-function-type X))

  is-acyclic-is-emb-diagonal-exponential :
    ({l' : Level} (X : UU l') → is-emb (diagonal-exponential X A)) →
    is-acyclic A
  is-acyclic-is-emb-diagonal-exponential e =
    is-acyclic-is-acyclic-map-terminal-map A
      ( is-acyclic-map-is-epimorphism
        ( terminal-map A)
        ( λ X →
          is-emb-triangle-is-equiv'
            ( diagonal-exponential X A)
            ( precomp (terminal-map A) X)
            ( map-inv-left-unit-law-function-type X)
            ( refl-htpy)
            ( is-equiv-map-inv-left-unit-law-function-type X)
            ( e X)))
```

### A type is acyclic if and only if the constant map from any identity type is an equivalence

More precisely, `A` is acyclic if and only if for all types `X` and elements
`x,y : X`, the map

```text
  Δ : (x ＝ y) → (A → x ＝ y)
```

is an equivalence.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-equiv-diagonal-exponential-Id-is-acyclic :
    is-acyclic A →
    {l' : Level} {X : UU l'} (x y : X) →
    is-equiv (diagonal-exponential (x ＝ y) A)
  is-equiv-diagonal-exponential-Id-is-acyclic ac {X = X} x y =
    is-equiv-htpy
      ( htpy-eq ∘ ap (diagonal-exponential X A) {x} {y})
      ( htpy-ap-diagonal-exponential-htpy-eq-diagonal-exponential-Id x y A)
      ( is-equiv-comp
        ( htpy-eq)
        ( ap (diagonal-exponential X A))
        ( is-emb-diagonal-exponential-is-acyclic A ac X x y)
        ( funext (diagonal-exponential X A x) (diagonal-exponential X A y)))

  is-acyclic-is-equiv-diagonal-exponential-Id :
    ( {l' : Level} {X : UU l'} (x y : X) →
      is-equiv (diagonal-exponential (x ＝ y) A)) →
    is-acyclic A
  is-acyclic-is-equiv-diagonal-exponential-Id h =
    is-acyclic-is-emb-diagonal-exponential A
      ( λ X x y →
        is-equiv-right-factor
          ( htpy-eq)
          ( ap (diagonal-exponential X A))
          ( funext (diagonal-exponential X A x) (diagonal-exponential X A y))
          ( is-equiv-htpy
            ( diagonal-exponential (x ＝ y) A)
            ( htpy-diagonal-exponential-Id-ap-diagonal-exponential-htpy-eq
              ( x)
              ( y)
              ( A))
            ( h x y)))
```

### A map is acyclic if and only if it is a dependent epimorphism { #a-map-is-acyclic-if-and-only-if-it-is-an-dependent-epimorphism }

<!-- The explicit id is there because it's linked to from the BdJR24 paper -->

The following diagram is a helpful illustration in the second proof:

```text
                        precomp f
       (b : B) → C b ------------- > (a : A) → C (f a)
             |                               ∧
             |                               |
     map-Π Δ |                               | ≃ [precomp with the equivalence
             |                               |        A ≃ Σ B (fiber f)     ]
             ∨               ind-Σ           |
 ((b : B) → fiber f b → C b) ----> (s : Σ B (fiber f)) → C (pr1 s)
                              ≃
                          [currying]
```

The left map is an embedding if `f` is an acyclic map, because the diagonal is
an embedding in this case.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-acyclic-map-is-dependent-epimorphism :
    is-dependent-epimorphism f → is-acyclic-map f
  is-acyclic-map-is-dependent-epimorphism e =
    is-acyclic-map-is-epimorphism f
      ( is-epimorphism-is-dependent-epimorphism f e)

  is-dependent-epimorphism-is-acyclic-map :
    is-acyclic-map f → is-dependent-epimorphism f
  is-dependent-epimorphism-is-acyclic-map ac C =
    is-emb-comp
      ( precomp-Π (map-inv-equiv-total-fiber f) (C ∘ pr1) ∘ ind-Σ)
      ( map-Π (λ b → diagonal-exponential (C b) (fiber f b)))
      ( is-emb-comp
        ( precomp-Π (map-inv-equiv-total-fiber f) (C ∘ pr1))
        ( ind-Σ)
        ( is-emb-is-equiv
          ( is-equiv-precomp-Π-is-equiv
            ( is-equiv-map-inv-equiv-total-fiber f) (C ∘ pr1)))
        ( is-emb-is-equiv is-equiv-ind-Σ))
      ( is-emb-map-Π
        ( λ b →
          is-emb-diagonal-exponential-is-acyclic (fiber f b) (ac b) (C b)))
```

In particular, every epimorphism is actually a dependent epimorphism.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  is-dependent-epimorphism-is-epimorphism :
    is-epimorphism f → is-dependent-epimorphism f
  is-dependent-epimorphism-is-epimorphism e =
    is-dependent-epimorphism-is-acyclic-map f
      ( is-acyclic-map-is-epimorphism f e)
```

### The class of acyclic maps is closed under composition and has the right cancellation property

Since the acyclic maps are precisely the epimorphisms this follows from the
corresponding facts about [epimorphisms](foundation.epimorphisms.md).

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  (g : B → C) (f : A → B)
  where

  is-acyclic-map-comp :
    is-acyclic-map g → is-acyclic-map f → is-acyclic-map (g ∘ f)
  is-acyclic-map-comp ag af =
    is-acyclic-map-is-epimorphism (g ∘ f)
      ( is-epimorphism-comp g f
        ( is-epimorphism-is-acyclic-map g ag)
        ( is-epimorphism-is-acyclic-map f af))

  is-acyclic-map-left-factor :
    is-acyclic-map (g ∘ f) → is-acyclic-map f → is-acyclic-map g
  is-acyclic-map-left-factor ac af =
    is-acyclic-map-is-epimorphism g
      ( is-epimorphism-left-factor g f
        ( is-epimorphism-is-acyclic-map (g ∘ f) ac)
        ( is-epimorphism-is-acyclic-map f af))
```

### Acyclic maps are closed under pushouts

**Proof:** Suppose we have a pushout square on the left in the diagram

```text
        g          j
   S -------> B -------> C
   |          |          |
 f |          | j        | id
   |          |          |
   ∨        ⌜ ∨          ∨
   A -------> C -------> C
        i          id
```

Then `j` is acyclic if and only if the right square is a pushout, which by
pushout pasting, is equivalent to the outer rectangle being a pushout. For an
arbitrary type `X` and `f` acyclic, we note that the following composite
computes to the identity:

```text
          cocone-map f (j ∘ g)
 (C → X) ---------------------> cocone f (j ∘ g) X
                             ̇= Σ (l : A → X) , Σ (r : C → X) , l ∘ f ~ r ∘ j ∘ g
     (using the left square)
                             ≃ Σ (l : A → X) , Σ (r : C → X) , l ∘ f ~ r ∘ i ∘ f
   (since f is acyclic/epic)
                             ≃ Σ (l : A → X) , Σ (r : C → X) , l ~ r ∘ i
                             ≃ Σ (r : C → X) , Σ (l : A → X) , l ~ r ∘ i
      (contracting at r ∘ i)
                             ≃ (C → X)
```

Therefore, `cocone-map f (j ∘ g)` is an equivalence and the outer rectangle is
indeed a pushout.

```agda
module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  equiv-cocone-postcomp-vertical-map-cocone :
    is-acyclic-map f →
    {l5 : Level} (X : UU l5) →
    cocone f (vertical-map-cocone f g c ∘ g) X ≃ (C → X)
  equiv-cocone-postcomp-vertical-map-cocone ac X =
    equivalence-reasoning
        cocone f (vertical-map-cocone f g c ∘ g) X
      ≃ cocone f (horizontal-map-cocone f g c ∘ f) X
        by
          equiv-tot
          ( λ u →
            equiv-tot
              ( λ v →
                equiv-concat-htpy'
                  ( u ∘ f)
                  ( λ s → ap v (inv-htpy (coherence-square-cocone f g c) s))))
      ≃ Σ ( A → X)
          ( λ u →
            Σ (C → X) (λ v → u ∘ f ＝ v ∘ horizontal-map-cocone f g c ∘ f))
        by equiv-tot ( λ u → equiv-tot ( λ v → equiv-eq-htpy))
      ≃ Σ (A → X) (λ u → Σ (C → X) (λ v → u ＝ v ∘ horizontal-map-cocone f g c))
        by
          equiv-tot
          ( λ u →
            equiv-tot
              ( λ v →
                inv-equiv-ap-is-emb (is-epimorphism-is-acyclic-map f ac X)))
      ≃ Σ (C → X) (λ v → Σ (A → X) (λ u → u ＝ v ∘ horizontal-map-cocone f g c))
        by
          equiv-left-swap-Σ
      ≃ (C → X)
        by
          equiv-pr1 (λ v → is-torsorial-Id' (v ∘ horizontal-map-cocone f g c))

  is-acyclic-map-vertical-map-cocone-is-pushout :
    is-pushout f g c →
    is-acyclic-map f →
    is-acyclic-map (vertical-map-cocone f g c)
  is-acyclic-map-vertical-map-cocone-is-pushout po ac =
    is-acyclic-map-is-epimorphism
      ( vertical-map-cocone f g c)
      ( is-epimorphism-universal-property-pushout
        ( vertical-map-cocone f g c)
        ( universal-property-pushout-right-universal-property-pushout-rectangle
          ( f)
          ( g)
          ( vertical-map-cocone f g c)
          ( c)
          ( cocone-codiagonal-map (vertical-map-cocone f g c))
          ( universal-property-pushout-is-pushout f g c po)
          ( λ X →
            is-equiv-right-factor
              ( map-equiv (equiv-cocone-postcomp-vertical-map-cocone ac X))
              ( cocone-map f
                ( vertical-map-cocone f g c ∘ g)
                ( cocone-comp-horizontal f g
                  ( vertical-map-cocone f g c)
                  ( c)
                  ( cocone-codiagonal-map (vertical-map-cocone f g c))))
              ( is-equiv-map-equiv
                ( equiv-cocone-postcomp-vertical-map-cocone ac X))
              ( is-equiv-id))))

module _
  {l1 l2 l3 l4 : Level} {S : UU l1} {A : UU l2} {B : UU l3}
  {C : UU l4} (f : S → A) (g : S → B) (c : cocone f g C)
  where

  is-acyclic-map-horizontal-map-cocone-is-pushout :
    is-pushout f g c →
    is-acyclic-map g →
    is-acyclic-map (horizontal-map-cocone f g c)
  is-acyclic-map-horizontal-map-cocone-is-pushout po =
    is-acyclic-map-vertical-map-cocone-is-pushout g f
      ( swap-cocone f g C c)
      ( is-pushout-swap-cocone-is-pushout f g C c po)
```

### Acyclic maps are closed under pullbacks

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-acyclic-map-vertical-map-cone-is-pullback :
    is-pullback f g c →
    is-acyclic-map g →
    is-acyclic-map (vertical-map-cone f g c)
  is-acyclic-map-vertical-map-cone-is-pullback pb ac a =
    is-acyclic-equiv
      ( map-fiber-vertical-map-cone f g c a ,
        is-fiberwise-equiv-map-fiber-vertical-map-cone-is-pullback f g c pb a)
      ( ac (f a))

module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  {X : UU l4} (f : A → X) (g : B → X) (c : cone f g C)
  where

  is-acyclic-map-horizontal-map-cone-is-pullback :
    is-pullback f g c →
    is-acyclic-map f →
    is-acyclic-map (horizontal-map-cone f g c)
  is-acyclic-map-horizontal-map-cone-is-pullback pb =
    is-acyclic-map-vertical-map-cone-is-pullback g f
      ( swap-cone f g c)
      ( is-pullback-swap-cone f g c pb)
```

### Acyclic types are closed under dependent pair types

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : A → UU l2)
  where

  is-acyclic-Σ :
    is-acyclic A → ((a : A) → is-acyclic (B a)) → is-acyclic (Σ A B)
  is-acyclic-Σ ac-A ac-B =
    is-acyclic-is-acyclic-map-terminal-map
      ( Σ A B)
      ( is-acyclic-map-comp
        ( terminal-map A)
        ( pr1)
        ( is-acyclic-map-terminal-map-is-acyclic A ac-A)
        ( λ a → is-acyclic-equiv (equiv-fiber-pr1 B a) (ac-B a)))
```

### Acyclic types are closed under binary products

```agda
module _
  {l1 l2 : Level} (A : UU l1) (B : UU l2)
  where

  is-acyclic-product :
    is-acyclic A → is-acyclic B → is-acyclic (A × B)
  is-acyclic-product ac-A ac-B =
    is-acyclic-is-acyclic-map-terminal-map
      ( A × B)
      ( is-acyclic-map-comp
        ( terminal-map B)
        ( pr2)
        ( is-acyclic-map-terminal-map-is-acyclic B ac-B)
        ( is-acyclic-map-horizontal-map-cone-is-pullback
          ( terminal-map A)
          ( terminal-map B)
          ( cone-cartesian-product A B)
          ( is-pullback-cartesian-product A B)
          ( is-acyclic-map-terminal-map-is-acyclic A ac-A)))
```

### Inhabited, locally acyclic types are acyclic

```agda
module _
  {l : Level} (A : UU l)
  where

  is-acyclic-inhabited-is-acyclic-Id :
    is-inhabited A →
    ((a b : A) → is-acyclic (a ＝ b)) →
    is-acyclic A
  is-acyclic-inhabited-is-acyclic-Id h l-ac =
    apply-universal-property-trunc-Prop h
      ( is-acyclic-Prop A)
      ( λ a →
        is-acyclic-is-acyclic-map-terminal-map A
          ( is-acyclic-map-left-factor
            ( terminal-map A)
            ( point a)
            ( is-acyclic-map-terminal-map-is-acyclic unit is-acyclic-unit)
            ( λ b → is-acyclic-equiv (compute-fiber-point a b) (l-ac a b))))
```

### Acyclic maps are closed under retracts

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y)
  where

  is-acyclic-map-retract-of :
    f retract-of-map g → is-acyclic-map g → is-acyclic-map f
  is-acyclic-map-retract-of R ac b =
    is-acyclic-retract-of
      ( retract-fiber-retract-map f g R b)
      ( ac (map-codomain-inclusion-retract-map f g R b))
```

## See also

- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
