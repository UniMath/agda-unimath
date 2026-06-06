# The universal property of quotient algebras

```agda
module universal-algebra.universal-property-quotient-algebras where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalence-relations
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.subtypes
open import foundation.universe-levels

open import universal-algebra.algebraic-theories
open import universal-algebra.algebras
open import universal-algebra.congruences
open import universal-algebra.homomorphisms-of-algebras
open import universal-algebra.isomorphisms-of-algebras
open import universal-algebra.reflecting-homomorphisms-congruences
open import universal-algebra.signatures
```

</details>

## Idea

The
{{#concept "universal property of quotients of algebras" Agda=is-quotient-Algebra}}
states that given [algebras](universal-algebra.algebras.md) `A` and `B` and a
[homomorphism](universal-algebra.homomorphisms-of-algebras.md) `φ : A → B`
[reflecting](universal-algebra.reflecting-homomorphisms-congruences.md) a
[congruence](universal-algebra.congruences.md) `R`, `B` is a quotient of `A` by
`R` if for any algebra `C`, the map precomposing homomorphisms `ψ : B → C` with
`φ` is an [equivalence](foundation-core.equivalences.md).

This universal property characterizes quotient algebras up to
[isomorphism](universal-algebra.isomorphisms-of-algebras.md).

## Definition

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R : congruence-Algebra l4 σ T A)
  (B : Algebra l5 σ T)
  (in-B@(hom-in-B , reflects-in-B) :
    reflecting-congruence-hom-Algebra σ T A R B)
  where

  precomp-reflecting-congruence-hom-Algebra :
    {l6 : Level} (C : Algebra l6 σ T) →
    hom-Algebra σ T B C →
    reflecting-congruence-hom-Algebra σ T A R C
  precomp-reflecting-congruence-hom-Algebra C φ =
    ( comp-hom-Algebra σ T A B C φ hom-in-B ,
      ap (map-hom-Algebra σ T B C φ) ∘ reflects-in-B)

  is-quotient-Algebra : UUω
  is-quotient-Algebra =
    {l6 : Level} (C : Algebra l6 σ T) →
    is-equiv (precomp-reflecting-congruence-hom-Algebra C)
```

## Properties

### The canonical homomorphism between two quotients of the same algebra by the same congruence

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R : congruence-Algebra l4 σ T A)
  (B : Algebra l5 σ T)
  (C : Algebra l6 σ T)
  (in-B : reflecting-congruence-hom-Algebra σ T A R B)
  (in-C : reflecting-congruence-hom-Algebra σ T A R C)
  (is-quotient-B : is-quotient-Algebra σ T A R B in-B)
  (is-quotient-C : is-quotient-Algebra σ T A R C in-C)
  where

  hom-is-quotient-Algebra : hom-Algebra σ T B C
  hom-is-quotient-Algebra = map-inv-is-equiv (is-quotient-B C) in-C
```

### The composition of the canonical homomorphisms between two quotients of the same algebra in each direction is the identity homomorphism

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R@(equiv-rel-R , _) : congruence-Algebra l4 σ T A)
  (B : Algebra l5 σ T)
  (C : Algebra l6 σ T)
  (in-B : reflecting-congruence-hom-Algebra σ T A R B)
  (in-C : reflecting-congruence-hom-Algebra σ T A R C)
  (is-quotient-B : is-quotient-Algebra σ T A R B in-B)
  (is-quotient-C : is-quotient-Algebra σ T A R C in-C)
  where

  abstract
    is-section-hom-is-quotient-Algebra :
      comp-hom-Algebra σ T C B C
        ( hom-is-quotient-Algebra σ T A R B C in-B in-C
          ( is-quotient-B)
          ( is-quotient-C))
        ( hom-is-quotient-Algebra σ T A R C B in-C in-B
          ( is-quotient-C)
          ( is-quotient-B)) ＝
      id-hom-Algebra σ T C
    is-section-hom-is-quotient-Algebra =
      is-injective-is-equiv
        ( is-quotient-C C)
        ( eq-type-subtype
          ( reflects-equivalence-relation-prop-hom-Algebra σ T A equiv-rel-R C)
          ( eq-htpy-hom-Algebra σ T A C _ _
            ( λ a →
              ( ap
                ( map-hom-Algebra σ T B C
                  ( hom-is-quotient-Algebra σ T A R B C in-B in-C
                    ( is-quotient-B)
                    ( is-quotient-C)))
                ( htpy-eq-hom-Algebra σ T A B _ (pr1 in-B)
                  ( ap pr1 (is-section-map-inv-is-equiv (is-quotient-C B) in-B))
                  ( a))) ∙
              ( htpy-eq-hom-Algebra σ T A C _ (pr1 in-C)
                ( ap pr1 (is-section-map-inv-is-equiv (is-quotient-B C) in-C))
                ( a)))))
```

### Any two quotient algebras are isomorphic

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (σ : signature l1)
  (T : Algebraic-Theory l2 σ)
  (A : Algebra l3 σ T)
  (R : congruence-Algebra l4 σ T A)
  (B : Algebra l5 σ T)
  (C : Algebra l6 σ T)
  (in-B : reflecting-congruence-hom-Algebra σ T A R B)
  (in-C : reflecting-congruence-hom-Algebra σ T A R C)
  (is-quotient-B : is-quotient-Algebra σ T A R B in-B)
  (is-quotient-C : is-quotient-Algebra σ T A R C in-C)
  where

  iso-is-quotient-Algebra : iso-Algebra σ T B C
  iso-is-quotient-Algebra =
    ( hom-is-quotient-Algebra σ T A R B C in-B in-C
        ( is-quotient-B)
        ( is-quotient-C) ,
      hom-is-quotient-Algebra σ T A R C B in-C in-B
        ( is-quotient-C)
        ( is-quotient-B) ,
      is-section-hom-is-quotient-Algebra σ T A R B C in-B in-C
        ( is-quotient-B)
        ( is-quotient-C) ,
      is-section-hom-is-quotient-Algebra σ T A R C B in-C in-B
        ( is-quotient-C)
        ( is-quotient-B))
```
