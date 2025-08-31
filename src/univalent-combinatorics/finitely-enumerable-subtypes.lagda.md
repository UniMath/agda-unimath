# Finitely enumerable subtypes

```agda
module univalent-combinatorics.finitely-enumerable-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.identity-types
open import foundation.images
open import foundation.images-subtypes
open import foundation.inhabited-subtypes
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import univalent-combinatorics.finitely-enumerable-types
```

</details>

## Idea

A [subtype](foundation.subtypes.md) `S` of a type `X` is
{{#concept "finitely enumerable" disambiguation="subtype" Agda=finitely-enumerable-subtype}}
if it is
[finitely enumerable](univalent-combinatorics.finitely-enumerable-types.md) as a
type.

## Definition

```agda
module _
  {l1 l2 : Level} {X : UU l1} (S : subtype l2 X)
  where

  finite-enumeration-subtype : UU (l1 ⊔ l2)
  finite-enumeration-subtype = finite-enumeration (type-subtype S)

  is-finitely-enumerable-prop-subtype : Prop (l1 ⊔ l2)
  is-finitely-enumerable-prop-subtype =
    is-finitely-enumerable-prop (type-subtype S)

  is-finitely-enumerable-subtype : UU (l1 ⊔ l2)
  is-finitely-enumerable-subtype = is-finitely-enumerable (type-subtype S)

finitely-enumerable-subtype :
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (l1 ⊔ lsuc l2)
finitely-enumerable-subtype l2 X =
  type-subtype (is-finitely-enumerable-prop-subtype {l2 = l2} {X = X})

module _
  {l1 l2 : Level} {X : UU l1} (S : finitely-enumerable-subtype l2 X)
  where

  subtype-finitely-enumerable-subtype : subtype l2 X
  subtype-finitely-enumerable-subtype = pr1 S

  is-finitely-enumerable-subtype-finitely-enumerable-subtype :
    is-finitely-enumerable-subtype subtype-finitely-enumerable-subtype
  is-finitely-enumerable-subtype-finitely-enumerable-subtype = pr2 S

  type-finitely-enumerable-subtype : UU (l1 ⊔ l2)
  type-finitely-enumerable-subtype =
    type-subtype subtype-finitely-enumerable-subtype

  inclusion-finitely-enumerable-subtype : type-finitely-enumerable-subtype → X
  inclusion-finitely-enumerable-subtype = pr1
```

## Properties

### The property of being an inhabited finitely enumerable subtype

```agda
module _
  {l1 l2 : Level} {X : UU l1} (S : finitely-enumerable-subtype l2 X)
  where

  is-inhabited-prop-finitely-enumerable-subtype : Prop (l1 ⊔ l2)
  is-inhabited-prop-finitely-enumerable-subtype =
    is-inhabited-subtype-Prop (subtype-finitely-enumerable-subtype S)

  is-inhabited-finitely-enumerable-subtype : UU (l1 ⊔ l2)
  is-inhabited-finitely-enumerable-subtype =
    is-inhabited-subtype (subtype-finitely-enumerable-subtype S)
```

### The image of a finitely enumerable subtype under a map is finitely enumerable

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (f : X → Y)
  (S : finitely-enumerable-subtype l3 X)
  where

  im-finitely-enumerable-subtype : subtype (l1 ⊔ l2 ⊔ l3) Y
  im-finitely-enumerable-subtype =
    im-subtype f (subtype-finitely-enumerable-subtype S)

  abstract
    is-finitely-enumerable-im-finitely-enumerable-subtype :
      is-finitely-enumerable-subtype im-finitely-enumerable-subtype
    is-finitely-enumerable-im-finitely-enumerable-subtype =
      rec-trunc-Prop
        ( is-finitely-enumerable-prop-subtype im-finitely-enumerable-subtype)
        ( λ (n , Fin-n->>S) →
          intro-exists
            ( n)
            ( ( λ i → map-unit-im (f ∘ pr1) (map-surjection Fin-n->>S i)) ,
              ( λ yim@(y , y∈im<f∘pr1∘Fin-n->>S>) →
                let
                  open
                    do-syntax-trunc-Prop
                      ( subtype-im
                        ( λ i →
                          map-unit-im (f ∘ pr1) (map-surjection Fin-n->>S i))
                        ( yim))
                in do
                  (s , fs=y) ← y∈im<f∘pr1∘Fin-n->>S>
                  (i , fini=s) ← is-surjective-map-surjection Fin-n->>S s
                  intro-exists i
                    ( eq-type-subtype
                      ( im-finitely-enumerable-subtype)
                      ( ap (f ∘ pr1) fini=s ∙ fs=y)))))
        ( is-finitely-enumerable-subtype-finitely-enumerable-subtype S)

  finitely-enumerable-subtype-im-finitely-enumerable-subtype :
    finitely-enumerable-subtype (l1 ⊔ l2 ⊔ l3) Y
  finitely-enumerable-subtype-im-finitely-enumerable-subtype =
    ( im-finitely-enumerable-subtype ,
      is-finitely-enumerable-im-finitely-enumerable-subtype)
```
