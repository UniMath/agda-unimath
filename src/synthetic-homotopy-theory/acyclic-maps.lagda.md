# Acyclic maps

```agda
module synthetic-homotopy-theory.acyclic-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.constant-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-epimorphisms
open import foundation.dependent-pair-types
open import foundation.dependent-universal-property-equivalences
open import foundation.embeddings
open import foundation.epimorphisms
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.homotopies
open import foundation.precomposition-dependent-functions
open import foundation.precomposition-functions
open import foundation.propositions
open import foundation.type-arithmetic-unit-type
open import foundation.unit-type
open import foundation.universal-property-dependent-pair-types
open import foundation.universe-levels

open import synthetic-homotopy-theory.acyclic-types
open import synthetic-homotopy-theory.codiagonals-of-maps
open import synthetic-homotopy-theory.suspensions-of-types
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

### A map is acyclic if and only if it is an [epimorphism](foundation.epimorphisms.md)

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
    is-acyclic A → is-acyclic-map (terminal-map {A = A})
  is-acyclic-map-terminal-map-is-acyclic ac u =
    is-acyclic-equiv (equiv-fiber-terminal-map u) ac

  is-acyclic-is-acyclic-map-terminal-map :
    is-acyclic-map (terminal-map {A = A}) → is-acyclic A
  is-acyclic-is-acyclic-map-terminal-map ac =
    is-acyclic-equiv inv-equiv-fiber-terminal-map-star (ac star)
```

### A type is acyclic if and only if the constant map from any type is an embedding

More precisely, `A` is acyclic if and only if for all types `X`, the map

```text
 const : X → (A → X)
```

is an embedding.

```agda
module _
  {l : Level} (A : UU l)
  where

  is-emb-const-is-acyclic :
    is-acyclic A →
    {l' : Level} (X : UU l') → is-emb (const A X)
  is-emb-const-is-acyclic ac X =
    is-emb-comp
      ( precomp terminal-map X)
      ( map-inv-left-unit-law-function-type X)
      ( is-epimorphism-is-acyclic-map terminal-map
        ( is-acyclic-map-terminal-map-is-acyclic A ac)
        ( X))
      ( is-emb-is-equiv (is-equiv-map-inv-left-unit-law-function-type X))

  is-acyclic-is-emb-const :
    ({l' : Level} (X : UU l') → is-emb (const A X)) →
    is-acyclic A
  is-acyclic-is-emb-const e =
    is-acyclic-is-acyclic-map-terminal-map A
      ( is-acyclic-map-is-epimorphism
        ( terminal-map)
        ( λ X →
          is-emb-triangle-is-equiv'
            ( const A X)
            ( precomp terminal-map X)
            ( map-inv-left-unit-law-function-type X)
            ( refl-htpy)
            ( is-equiv-map-inv-left-unit-law-function-type X)
            ( e X)))
```

### A map is acyclic if and only if it is an [dependent epimorphism](foundation.dependent-epimorphisms.md)

The following diagram is a helpful illustration in the second proof:

```text
                        precomp f
       (b : B) → C b ------------- > (a : A) → C (f a)
             |                               ^
             |                               |
 map-Π const |                               | ≃ [precomp with the equivalence
             |                               |        A ≃ Σ B (fiber f)     ]
             v               ind-Σ           |
 ((b : B) → fiber f b → C b) ----> (s : Σ B (fiber f)) → C (pr1 s)
                              ≃
                          [currying]
```

The left map is an embedding if f is an acyclic map, because const is an
embedding in this case.

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
      ( map-Π (λ b → const (fiber f b) (C b)))
      ( is-emb-comp
        ( precomp-Π (map-inv-equiv-total-fiber f) (C ∘ pr1))
        ( ind-Σ)
        ( is-emb-is-equiv
          ( is-equiv-precomp-Π-is-equiv
            ( is-equiv-map-inv-equiv-total-fiber f) (C ∘ pr1)))
        ( is-emb-is-equiv is-equiv-ind-Σ))
      ( is-emb-map-Π (λ b → is-emb-const-is-acyclic (fiber f b) (ac b) (C b)))
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

## See also

- [Dependent epimorphisms](foundation.dependent-epimorphisms.md)
- [Epimorphisms](foundation.epimorphisms.md)
- [Epimorphisms with respect to sets](foundation.epimorphisms-with-respect-to-sets.md)
- [Epimorphisms with respect to truncated types](foundation.epimorphisms-with-respect-to-truncated-types.md)

### Table of files related to cyclic types, groups, and rings

{{#include tables/cyclic-types.md}}
