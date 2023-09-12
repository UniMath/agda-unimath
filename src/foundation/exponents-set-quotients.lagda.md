# Exponents of set quotients

```agda
{-# OPTIONS --lossy-unification #-}

module foundation.exponents-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.functoriality-set-quotients
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.universal-property-set-quotients
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.equivalence-relations
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.whiskering-homotopies
```

</details>

## Idea

Given a type `A` equipped with an equivalence relation `R` and a type `X`, the
set quotient

```text
  (X → A) / ~
```

where `f ~ g := (x : A) → R (f x) (g x)`, embeds into the type `X → A/R`. This
embedding for every `X`, `A`, and `R` if and only if the axiom of choice holds.

Consequently, we get embeddings

```text
  ((hom-Equivalence-Relation R S) / ~) ↪ ((A/R) → (B/S))
```

for any two equivalence relations `R` on `A` and `S` on `B`.

## Definitions

### The canonical equivalence relation on `X → A`

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} (R : Equivalence-Relation l3 A)
  where

  rel-function-type : Relation-Prop (l1 ⊔ l3) (X → A)
  rel-function-type f g =
    Π-Prop X (λ x → prop-Equivalence-Relation R (f x) (g x))

  sim-function-type : (f g : X → A) → UU (l1 ⊔ l3)
  sim-function-type = type-Relation-Prop rel-function-type

  refl-sim-function-type : is-reflexive sim-function-type
  refl-sim-function-type f x = refl-Equivalence-Relation R (f x)

  symmetric-sim-function-type : is-symmetric sim-function-type
  symmetric-sim-function-type f g r x =
    symmetric-Equivalence-Relation R (f x) (g x) (r x)

  transitive-sim-function-type : is-transitive sim-function-type
  transitive-sim-function-type f g h r s x =
    transitive-Equivalence-Relation R (f x) (g x) (h x) (r x) (s x)

  eq-rel-function-type : Equivalence-Relation (l1 ⊔ l3) (X → A)
  pr1 eq-rel-function-type = rel-function-type
  pr1 (pr2 eq-rel-function-type) = refl-sim-function-type
  pr1 (pr2 (pr2 eq-rel-function-type)) = symmetric-sim-function-type
  pr2 (pr2 (pr2 eq-rel-function-type)) = transitive-sim-function-type

  map-exponent-reflecting-map-Equivalence-Relation :
    {l4 : Level} {B : UU l4} →
    reflecting-map-Equivalence-Relation R B → (X → A) → (X → B)
  map-exponent-reflecting-map-Equivalence-Relation q =
    postcomp X (map-reflecting-map-Equivalence-Relation R q)

  reflects-exponent-reflecting-map-Equivalence-Relation :
    {l4 : Level} {B : UU l4} (q : reflecting-map-Equivalence-Relation R B) →
    reflects-Equivalence-Relation eq-rel-function-type
      ( map-exponent-reflecting-map-Equivalence-Relation q)
  reflects-exponent-reflecting-map-Equivalence-Relation q {f} {g} H =
    eq-htpy (λ x → reflects-map-reflecting-map-Equivalence-Relation R q (H x))

  exponent-reflecting-map-Equivalence-Relation :
    {l4 : Level} {B : UU l4} →
    reflecting-map-Equivalence-Relation R B →
    reflecting-map-Equivalence-Relation eq-rel-function-type (X → B)
  pr1 (exponent-reflecting-map-Equivalence-Relation q) =
    map-exponent-reflecting-map-Equivalence-Relation q
  pr2 (exponent-reflecting-map-Equivalence-Relation q) =
    reflects-exponent-reflecting-map-Equivalence-Relation q

  module _
    {l4 l5 : Level}
    (Q : Set l4)
    (q : reflecting-map-Equivalence-Relation eq-rel-function-type (type-Set Q))
    (Uq : {l : Level} → is-set-quotient l eq-rel-function-type Q q)
    (QR : Set l5) (qR : reflecting-map-Equivalence-Relation R (type-Set QR))
    (UqR : {l : Level} → is-set-quotient l R QR qR)
    where

    unique-inclusion-is-set-quotient-eq-rel-function-type :
      is-contr
        ( Σ ( type-Set Q → (X → type-Set QR))
            ( λ h →
              ( h ∘
                map-reflecting-map-Equivalence-Relation eq-rel-function-type q)
              ~
              ( map-exponent-reflecting-map-Equivalence-Relation qR)))
    unique-inclusion-is-set-quotient-eq-rel-function-type =
      universal-property-set-quotient-is-set-quotient
        ( eq-rel-function-type)
        ( Q)
        ( q)
        ( Uq)
        ( function-Set X QR)
        ( exponent-reflecting-map-Equivalence-Relation qR)

    map-inclusion-is-set-quotient-eq-rel-function-type :
      type-Set Q → (X → type-Set QR)
    map-inclusion-is-set-quotient-eq-rel-function-type =
      map-universal-property-set-quotient-is-set-quotient
        ( eq-rel-function-type)
        ( Q)
        ( q)
        ( Uq)
        ( function-Set X QR)
        ( exponent-reflecting-map-Equivalence-Relation qR)

    triangle-inclusion-is-set-quotient-eq-rel-function-type :
      ( ( map-inclusion-is-set-quotient-eq-rel-function-type) ∘
        ( map-reflecting-map-Equivalence-Relation eq-rel-function-type q)) ~
      ( map-exponent-reflecting-map-Equivalence-Relation qR)
    triangle-inclusion-is-set-quotient-eq-rel-function-type =
      triangle-universal-property-set-quotient-is-set-quotient
        ( eq-rel-function-type)
        ( Q)
        ( q)
        ( Uq)
        ( function-Set X QR)
        ( exponent-reflecting-map-Equivalence-Relation qR)
```

### An equivalence relation on relation preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  where

  rel-hom-Equivalence-Relation :
    Relation-Prop (l1 ⊔ l4) (hom-Equivalence-Relation R S)
  rel-hom-Equivalence-Relation f g =
    rel-function-type A S
      ( map-hom-Equivalence-Relation R S f)
      ( map-hom-Equivalence-Relation R S g)

  sim-hom-Equivalence-Relation :
    (f g : hom-Equivalence-Relation R S) → UU (l1 ⊔ l4)
  sim-hom-Equivalence-Relation f g =
    sim-function-type A S
      ( map-hom-Equivalence-Relation R S f)
      ( map-hom-Equivalence-Relation R S g)

  refl-sim-hom-Equivalence-Relation : is-reflexive sim-hom-Equivalence-Relation
  refl-sim-hom-Equivalence-Relation f =
    refl-sim-function-type A S (map-hom-Equivalence-Relation R S f)

  symmetric-sim-hom-Equivalence-Relation :
    is-symmetric sim-hom-Equivalence-Relation
  symmetric-sim-hom-Equivalence-Relation f g =
    symmetric-sim-function-type A S
      ( map-hom-Equivalence-Relation R S f)
      ( map-hom-Equivalence-Relation R S g)

  transitive-sim-hom-Equivalence-Relation :
    is-transitive sim-hom-Equivalence-Relation
  transitive-sim-hom-Equivalence-Relation f g h =
    transitive-sim-function-type A S
      ( map-hom-Equivalence-Relation R S f)
      ( map-hom-Equivalence-Relation R S g)
      ( map-hom-Equivalence-Relation R S h)

  eq-rel-hom-Equivalence-Relation :
    Equivalence-Relation (l1 ⊔ l4) (hom-Equivalence-Relation R S)
  pr1 eq-rel-hom-Equivalence-Relation = rel-hom-Equivalence-Relation
  pr1 (pr2 eq-rel-hom-Equivalence-Relation) = refl-sim-hom-Equivalence-Relation
  pr1 (pr2 (pr2 eq-rel-hom-Equivalence-Relation)) =
    symmetric-sim-hom-Equivalence-Relation
  pr2 (pr2 (pr2 eq-rel-hom-Equivalence-Relation)) =
    transitive-sim-hom-Equivalence-Relation
```

### The universal reflecting map from `hom-Equivalence-Relation R S` to `A/R → B/S`

#### First variant using only the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  (QR : Set l3) (qR : reflecting-map-Equivalence-Relation R (type-Set QR))
  (UqR : {l : Level} → is-set-quotient l R QR qR)
  {B : UU l4} (S : Equivalence-Relation l5 B)
  (QS : Set l6) (qS : reflecting-map-Equivalence-Relation S (type-Set QS))
  (UqS : {l : Level} → is-set-quotient l S QS qS)
  where

  universal-map-is-set-quotient-hom-Equivalence-Relation :
    hom-Equivalence-Relation R S → type-hom-Set QR QS
  universal-map-is-set-quotient-hom-Equivalence-Relation =
    map-is-set-quotient R QR qR S QS qS UqR UqS

  reflects-universal-map-is-set-quotient-hom-Equivalence-Relation :
    reflects-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( universal-map-is-set-quotient-hom-Equivalence-Relation)
  reflects-universal-map-is-set-quotient-hom-Equivalence-Relation {f} {g} s =
    eq-htpy
      ( ind-is-set-quotient R QR qR UqR
        ( λ x →
          Id-Prop QS
            ( map-is-set-quotient R QR qR S QS qS UqR UqS f x)
            ( map-is-set-quotient R QR qR S QS qS UqR UqS g x))
        ( λ a →
          coherence-square-map-is-set-quotient R QR qR S QS qS UqR UqS f a ∙
          ( ( apply-effectiveness-is-set-quotient' S QS qS UqS (s a)) ∙
            ( inv
              ( coherence-square-map-is-set-quotient
                R QR qR S QS qS UqR UqS g a)))))

  universal-reflecting-map-is-set-quotient-hom-Equivalence-Relation :
    reflecting-map-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( type-hom-Set QR QS)
  pr1 universal-reflecting-map-is-set-quotient-hom-Equivalence-Relation =
    universal-map-is-set-quotient-hom-Equivalence-Relation
  pr2 universal-reflecting-map-is-set-quotient-hom-Equivalence-Relation =
    reflects-universal-map-is-set-quotient-hom-Equivalence-Relation
```

#### Second variant using the designated set quotients

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  where

  universal-reflecting-map-set-quotient-hom-Equivalence-Relation :
    reflecting-map-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( set-quotient R → set-quotient S)
  universal-reflecting-map-set-quotient-hom-Equivalence-Relation =
    universal-reflecting-map-is-set-quotient-hom-Equivalence-Relation
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( λ {l} → is-set-quotient-set-quotient R {l})
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( λ {l} → is-set-quotient-set-quotient S {l})

  universal-map-set-quotient-hom-Equivalence-Relation :
    hom-Equivalence-Relation R S → set-quotient R → set-quotient S
  universal-map-set-quotient-hom-Equivalence-Relation =
    map-reflecting-map-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( universal-reflecting-map-set-quotient-hom-Equivalence-Relation)

  reflects-universal-map-set-quotient-hom-Equivalence-Relation :
    reflects-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( universal-map-set-quotient-hom-Equivalence-Relation)
  reflects-universal-map-set-quotient-hom-Equivalence-Relation =
    reflects-map-reflecting-map-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( universal-reflecting-map-set-quotient-hom-Equivalence-Relation)
```

## Properties

### The inclusion of the quotient `(X → A)/~` into `X → A/R` is an embedding

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : UU l1)
  {A : UU l2} (R : Equivalence-Relation l3 A)
  (Q : Set l4)
  (q :
    reflecting-map-Equivalence-Relation
      ( eq-rel-function-type X R)
      ( type-Set Q))
  (Uq : {l : Level} → is-set-quotient l (eq-rel-function-type X R) Q q)
  (QR : Set l5) (qR : reflecting-map-Equivalence-Relation R (type-Set QR))
  (UqR : {l : Level} → is-set-quotient l R QR qR)
  where

  is-emb-inclusion-is-set-quotient-eq-rel-function-type :
    is-emb
      ( map-inclusion-is-set-quotient-eq-rel-function-type X R Q q Uq QR qR UqR)
  is-emb-inclusion-is-set-quotient-eq-rel-function-type =
    is-emb-map-universal-property-set-quotient-is-set-quotient
      ( eq-rel-function-type X R)
      ( Q)
      ( q)
      ( Uq)
      ( function-Set X QR)
      ( exponent-reflecting-map-Equivalence-Relation X R qR)
      ( λ g h p x →
        apply-effectiveness-is-set-quotient R QR qR UqR (htpy-eq p x))
```

### The extension of the universal map from `hom-Equivalence-Relation R S` to `A/R → B/S` to the quotient is an embedding

#### First variant using only the universal property of the set quotient

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  (QR : Set l3) (qR : reflecting-map-Equivalence-Relation R (type-Set QR))
  (UR : {l : Level} → is-set-quotient l R QR qR)
  {B : UU l4} (S : Equivalence-Relation l5 B)
  (QS : Set l6) (qS : reflecting-map-Equivalence-Relation S (type-Set QS))
  (US : {l : Level} → is-set-quotient l S QS qS)
  (QH : Set l7)
  (qH :
    reflecting-map-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( type-Set QH))
  (UH :
    {l : Level} →
    is-set-quotient l (eq-rel-hom-Equivalence-Relation R S) QH qH)
  where

  unique-inclusion-is-set-quotient-hom-Equivalence-Relation :
    is-contr
      ( Σ ( type-hom-Set QH (hom-Set QR QS))
          ( λ μ →
            ( μ ∘
              map-reflecting-map-Equivalence-Relation
                ( eq-rel-hom-Equivalence-Relation R S)
                ( qH)) ~
            ( universal-map-is-set-quotient-hom-Equivalence-Relation
                R QR qR UR S QS qS US)))
  unique-inclusion-is-set-quotient-hom-Equivalence-Relation =
    universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Equivalence-Relation R S)
      ( QH)
      ( qH)
      ( UH)
      ( hom-Set QR QS)
      ( universal-reflecting-map-is-set-quotient-hom-Equivalence-Relation
        R QR qR UR S QS qS US)

  inclusion-is-set-quotient-hom-Equivalence-Relation :
    type-hom-Set QH (hom-Set QR QS)
  inclusion-is-set-quotient-hom-Equivalence-Relation =
    pr1 (center (unique-inclusion-is-set-quotient-hom-Equivalence-Relation))

  triangle-inclusion-is-set-quotient-hom-Equivalence-Relation :
    ( inclusion-is-set-quotient-hom-Equivalence-Relation ∘
      map-reflecting-map-Equivalence-Relation
        ( eq-rel-hom-Equivalence-Relation R S)
        ( qH)) ~
    ( universal-map-is-set-quotient-hom-Equivalence-Relation
        R QR qR UR S QS qS US)
  triangle-inclusion-is-set-quotient-hom-Equivalence-Relation =
    pr2 (center (unique-inclusion-is-set-quotient-hom-Equivalence-Relation))

  is-emb-inclusion-is-set-quotient-hom-Equivalence-Relation :
    is-emb inclusion-is-set-quotient-hom-Equivalence-Relation
  is-emb-inclusion-is-set-quotient-hom-Equivalence-Relation =
    is-emb-map-universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Equivalence-Relation R S)
      ( QH)
      ( qH)
      ( UH)
      ( hom-Set QR QS)
      ( universal-reflecting-map-is-set-quotient-hom-Equivalence-Relation
        R QR qR UR S QS qS US)
      ( λ g h p a →
        apply-effectiveness-is-set-quotient S QS qS US
          ( ( inv-htpy
              ( coherence-square-map-is-set-quotient R QR qR S QS qS UR US g) ∙h
              ( ( htpy-eq p ·r map-reflecting-map-Equivalence-Relation R qR) ∙h
                ( coherence-square-map-is-set-quotient
                  R QR qR S QS qS UR US h)))
            ( a)))

  emb-inclusion-is-set-quotient-hom-Equivalence-Relation :
    type-Set QH ↪ type-hom-Set QR QS
  pr1 emb-inclusion-is-set-quotient-hom-Equivalence-Relation =
    inclusion-is-set-quotient-hom-Equivalence-Relation
  pr2 emb-inclusion-is-set-quotient-hom-Equivalence-Relation =
    is-emb-inclusion-is-set-quotient-hom-Equivalence-Relation
```

#### Second variant using the official set quotients

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Equivalence-Relation l2 A)
  {B : UU l3} (S : Equivalence-Relation l4 B)
  where

  quotient-hom-Equivalence-Relation-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-hom-Equivalence-Relation-Set =
    quotient-Set (eq-rel-hom-Equivalence-Relation R S)

  set-quotient-hom-Equivalence-Relation : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  set-quotient-hom-Equivalence-Relation =
    type-Set quotient-hom-Equivalence-Relation-Set

  is-set-set-quotient-hom-Equivalence-Relation :
    is-set set-quotient-hom-Equivalence-Relation
  is-set-set-quotient-hom-Equivalence-Relation =
    is-set-type-Set quotient-hom-Equivalence-Relation-Set

  reflecting-map-quotient-map-hom-Equivalence-Relation :
    reflecting-map-Equivalence-Relation
      ( eq-rel-hom-Equivalence-Relation R S)
      ( set-quotient-hom-Equivalence-Relation)
  reflecting-map-quotient-map-hom-Equivalence-Relation =
    reflecting-map-quotient-map (eq-rel-hom-Equivalence-Relation R S)

  quotient-map-hom-Equivalence-Relation :
    hom-Equivalence-Relation R S → set-quotient-hom-Equivalence-Relation
  quotient-map-hom-Equivalence-Relation =
    quotient-map (eq-rel-hom-Equivalence-Relation R S)

  is-set-quotient-set-quotient-hom-Equivalence-Relation :
    {l : Level} →
    is-set-quotient l
      ( eq-rel-hom-Equivalence-Relation R S)
      ( quotient-hom-Equivalence-Relation-Set)
      ( reflecting-map-quotient-map-hom-Equivalence-Relation)
  is-set-quotient-set-quotient-hom-Equivalence-Relation =
    is-set-quotient-set-quotient (eq-rel-hom-Equivalence-Relation R S)

  unique-inclusion-set-quotient-hom-Equivalence-Relation :
    is-contr
      ( Σ ( set-quotient-hom-Equivalence-Relation →
            set-quotient R → set-quotient S)
          ( λ μ →
            ( μ ∘ quotient-map (eq-rel-hom-Equivalence-Relation R S)) ~
            ( universal-map-set-quotient-hom-Equivalence-Relation R S)))
  unique-inclusion-set-quotient-hom-Equivalence-Relation =
    universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Equivalence-Relation R S)
      ( quotient-hom-Equivalence-Relation-Set)
      ( reflecting-map-quotient-map-hom-Equivalence-Relation)
      ( is-set-quotient-set-quotient-hom-Equivalence-Relation)
      ( hom-Set (quotient-Set R) (quotient-Set S))
      ( universal-reflecting-map-set-quotient-hom-Equivalence-Relation R S)

  inclusion-set-quotient-hom-Equivalence-Relation :
    set-quotient (eq-rel-hom-Equivalence-Relation R S) →
    set-quotient R → set-quotient S
  inclusion-set-quotient-hom-Equivalence-Relation =
    pr1 (center (unique-inclusion-set-quotient-hom-Equivalence-Relation))

  triangle-inclusion-set-quotient-hom-Equivalence-Relation :
    ( inclusion-set-quotient-hom-Equivalence-Relation ∘
      quotient-map (eq-rel-hom-Equivalence-Relation R S)) ~
    ( universal-map-set-quotient-hom-Equivalence-Relation R S)
  triangle-inclusion-set-quotient-hom-Equivalence-Relation =
    pr2 (center (unique-inclusion-set-quotient-hom-Equivalence-Relation))

  is-emb-inclusion-set-quotient-hom-Equivalence-Relation :
    is-emb inclusion-set-quotient-hom-Equivalence-Relation
  is-emb-inclusion-set-quotient-hom-Equivalence-Relation =
    is-emb-map-universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Equivalence-Relation R S)
      ( quotient-hom-Equivalence-Relation-Set)
      ( reflecting-map-quotient-map-hom-Equivalence-Relation)
      ( is-set-quotient-set-quotient-hom-Equivalence-Relation)
      ( hom-Set (quotient-Set R) (quotient-Set S))
      ( universal-reflecting-map-set-quotient-hom-Equivalence-Relation R S)
      ( λ g h p a →
        apply-effectiveness-quotient-map S
          ( ( inv-htpy
              ( coherence-square-map-set-quotient R S g) ∙h
              ( ( htpy-eq p ·r quotient-map R) ∙h
                ( coherence-square-map-set-quotient
                  R S h)))
            ( a)))

  emb-inclusion-set-quotient-hom-Equivalence-Relation :
    set-quotient (eq-rel-hom-Equivalence-Relation R S) ↪
    ( set-quotient R → set-quotient S)
  pr1 emb-inclusion-set-quotient-hom-Equivalence-Relation =
    inclusion-set-quotient-hom-Equivalence-Relation
  pr2 emb-inclusion-set-quotient-hom-Equivalence-Relation =
    is-emb-inclusion-set-quotient-hom-Equivalence-Relation
```
