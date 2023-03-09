# Exponents of set quotients

```agda
{-# OPTIONS --lossy-unification #-}
```

```agda
module foundation.exponents-set-quotients where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equivalence-relations
open import foundation.function-extensionality
open import foundation.functions
open import foundation.functoriality-set-quotients
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.propositions
open import foundation.reflecting-maps-equivalence-relations
open import foundation.set-quotients
open import foundation.sets
open import foundation.surjective-maps
open import foundation.universal-property-set-quotients
open import foundation.universe-levels
```

</details>

## Idea

Given a type `A` equipped with an equivalence relation `R` and a type `X`, the set quotient

```md
  (X → A) / ~
```

where `f ~ g := (x : A) → R (f x) (g x)`, embeds into the type `X → A/R`. This embedding for every `X`, `A`, and `R` if and only if the axiom of choice holds.

Consequently, we get embeddings

```md
  ((hom-Eq-Rel R S) / ~) ↪ ((A/R) → (B/S))
```

for any two equivalence relations `R` on `A` and `S` on `B`.

## Definitions

### The canonical equivalence relation on `X → A`

```agda
module _
  {l1 l2 l3 : Level} (X : UU l1) {A : UU l2} (R : Eq-Rel l3 A)
  where

  rel-function-type : Rel-Prop (l1 ⊔ l3) (X → A)
  rel-function-type f g = Π-Prop X (λ x → prop-Eq-Rel R (f x) (g x))

  sim-function-type : (f g : X → A) → UU (l1 ⊔ l3)
  sim-function-type = type-Rel-Prop rel-function-type

  refl-sim-function-type : (f : X → A) → sim-function-type f f
  refl-sim-function-type f x = refl-Eq-Rel R

  symm-sim-function-type :
    (f g : X → A) → sim-function-type f g → sim-function-type g f
  symm-sim-function-type f g r x = symm-Eq-Rel R (r x)

  trans-sim-function-type :
    (f g h : X → A) →
    sim-function-type f g → sim-function-type g h → sim-function-type f h
  trans-sim-function-type f g h r s x = trans-Eq-Rel R (r x) (s x)

  eq-rel-function-type : Eq-Rel (l1 ⊔ l3) (X → A)
  pr1 eq-rel-function-type = rel-function-type
  pr1 (pr2 eq-rel-function-type) {f} = refl-sim-function-type f
  pr1 (pr2 (pr2 eq-rel-function-type)) {f} {g} = symm-sim-function-type f g
  pr2 (pr2 (pr2 eq-rel-function-type)) {f} {g} {h} =
    trans-sim-function-type f g h

  map-exponent-reflecting-map-Eq-Rel :
    {l4 : Level} {B : UU l4} → reflecting-map-Eq-Rel R B → (X → A) → (X → B)
  map-exponent-reflecting-map-Eq-Rel q =
    postcomp X (map-reflecting-map-Eq-Rel R q)

  reflects-exponent-reflecting-map-Eq-Rel :
    {l4 : Level} {B : UU l4} (q : reflecting-map-Eq-Rel R B) →
    reflects-Eq-Rel eq-rel-function-type (map-exponent-reflecting-map-Eq-Rel q)
  reflects-exponent-reflecting-map-Eq-Rel q {f} {g} H =
    eq-htpy (λ x → reflects-map-reflecting-map-Eq-Rel R q (H x))

  exponent-reflecting-map-Eq-Rel :
    {l4 : Level} {B : UU l4} →
    reflecting-map-Eq-Rel R B →
    reflecting-map-Eq-Rel eq-rel-function-type (X → B)
  pr1 (exponent-reflecting-map-Eq-Rel q) = map-exponent-reflecting-map-Eq-Rel q
  pr2 (exponent-reflecting-map-Eq-Rel q) =
    reflects-exponent-reflecting-map-Eq-Rel q

  module _
    {l4 l5 : Level}
    (Q : Set l4) (q : reflecting-map-Eq-Rel eq-rel-function-type (type-Set Q))
    (Uq : {l : Level} → is-set-quotient l eq-rel-function-type Q q)
    (QR : Set l5) (qR : reflecting-map-Eq-Rel R (type-Set QR))
    (UqR : {l : Level} → is-set-quotient l R QR qR)
    where

    unique-inclusion-is-set-quotient-eq-rel-function-type :
      is-contr
        ( Σ ( type-Set Q → (X → type-Set QR))
            ( λ h →
              ( h ∘ map-reflecting-map-Eq-Rel eq-rel-function-type q) ~
              ( map-exponent-reflecting-map-Eq-Rel qR)))
    unique-inclusion-is-set-quotient-eq-rel-function-type =
      universal-property-set-quotient-is-set-quotient
        ( eq-rel-function-type)
        ( Q)
        ( q)
        ( Uq)
        ( function-Set X QR)
        ( exponent-reflecting-map-Eq-Rel qR)

    map-inclusion-is-set-quotient-eq-rel-function-type :
      type-Set Q → (X → type-Set QR)
    map-inclusion-is-set-quotient-eq-rel-function-type =
      map-universal-property-set-quotient-is-set-quotient
        ( eq-rel-function-type)
        ( Q)
        ( q)
        ( Uq)
        ( function-Set X QR)
        ( exponent-reflecting-map-Eq-Rel qR)

    triangle-inclusion-is-set-quotient-eq-rel-function-type :
      ( ( map-inclusion-is-set-quotient-eq-rel-function-type) ∘
        ( map-reflecting-map-Eq-Rel eq-rel-function-type q)) ~
      ( map-exponent-reflecting-map-Eq-Rel qR)
    triangle-inclusion-is-set-quotient-eq-rel-function-type =
      triangle-universal-property-set-quotient-is-set-quotient
        ( eq-rel-function-type)
        ( Q)
        ( q)
        ( Uq)
        ( function-Set X QR)
        ( exponent-reflecting-map-Eq-Rel qR)
```

### An equivalence relation on relation preserving maps

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A) {B : UU l3} (S : Eq-Rel l4 B)
  where

  rel-hom-Eq-Rel : Rel-Prop (l1 ⊔ l4) (hom-Eq-Rel R S)
  rel-hom-Eq-Rel f g =
    rel-function-type A S (map-hom-Eq-Rel R S f) (map-hom-Eq-Rel R S g)

  sim-hom-Eq-Rel : (f g : hom-Eq-Rel R S) → UU (l1 ⊔ l4)
  sim-hom-Eq-Rel f g =
    sim-function-type A S (map-hom-Eq-Rel R S f) (map-hom-Eq-Rel R S g)

  refl-sim-hom-Eq-Rel :
    (f : hom-Eq-Rel R S) → sim-hom-Eq-Rel f f
  refl-sim-hom-Eq-Rel f =
    refl-sim-function-type A S (map-hom-Eq-Rel R S f)

  symm-sim-hom-Eq-Rel :
    (f g : hom-Eq-Rel R S) → sim-hom-Eq-Rel f g → sim-hom-Eq-Rel g f
  symm-sim-hom-Eq-Rel f g =
    symm-sim-function-type A S (map-hom-Eq-Rel R S f) (map-hom-Eq-Rel R S g)

  trans-sim-hom-Eq-Rel :
    (f g h : hom-Eq-Rel R S) →
    sim-hom-Eq-Rel f g → sim-hom-Eq-Rel g h → sim-hom-Eq-Rel f h
  trans-sim-hom-Eq-Rel f g h =
    trans-sim-function-type A S
      ( map-hom-Eq-Rel R S f)
      ( map-hom-Eq-Rel R S g)
      ( map-hom-Eq-Rel R S h)

  eq-rel-hom-Eq-Rel :
    Eq-Rel (l1 ⊔ l4) (hom-Eq-Rel R S)
  pr1 eq-rel-hom-Eq-Rel = rel-hom-Eq-Rel
  pr1 (pr2 eq-rel-hom-Eq-Rel) {f} = refl-sim-hom-Eq-Rel f
  pr1 (pr2 (pr2 eq-rel-hom-Eq-Rel)) {f} {g} = symm-sim-hom-Eq-Rel f g
  pr2 (pr2 (pr2 eq-rel-hom-Eq-Rel)) {f} {g} {h} = trans-sim-hom-Eq-Rel f g h
```

### The universal reflecting map from `hom-Eq-Rel R S` to `A/R → B/S`

#### First variant using only the universal property of set quotients

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (qR : reflecting-map-Eq-Rel R (type-Set QR))
  (UqR : {l : Level} → is-set-quotient l R QR qR)
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (qS : reflecting-map-Eq-Rel S (type-Set QS))
  (UqS : {l : Level} → is-set-quotient l S QS qS)
  where

  universal-map-is-set-quotient-hom-Eq-Rel :
    hom-Eq-Rel R S → type-hom-Set QR QS
  universal-map-is-set-quotient-hom-Eq-Rel =
    map-is-set-quotient R QR qR S QS qS UqR UqS

  reflects-universal-map-is-set-quotient-hom-Eq-Rel :
    reflects-Eq-Rel
      ( eq-rel-hom-Eq-Rel R S)
      ( universal-map-is-set-quotient-hom-Eq-Rel)
  reflects-universal-map-is-set-quotient-hom-Eq-Rel {f} {g} s =
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

  universal-reflecting-map-is-set-quotient-hom-Eq-Rel :
    reflecting-map-Eq-Rel (eq-rel-hom-Eq-Rel R S) (type-hom-Set QR QS)
  pr1 universal-reflecting-map-is-set-quotient-hom-Eq-Rel =
    universal-map-is-set-quotient-hom-Eq-Rel
  pr2 universal-reflecting-map-is-set-quotient-hom-Eq-Rel =
    reflects-universal-map-is-set-quotient-hom-Eq-Rel
```

#### Second variant using the designated set quotients

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  where

  universal-reflecting-map-set-quotient-hom-Eq-Rel :
    reflecting-map-Eq-Rel
      ( eq-rel-hom-Eq-Rel R S)
      ( set-quotient R → set-quotient S)
  universal-reflecting-map-set-quotient-hom-Eq-Rel =
    universal-reflecting-map-is-set-quotient-hom-Eq-Rel
      ( R)
      ( quotient-Set R)
      ( reflecting-map-quotient-map R)
      ( λ {l} → is-set-quotient-set-quotient R {l})
      ( S)
      ( quotient-Set S)
      ( reflecting-map-quotient-map S)
      ( λ {l} → is-set-quotient-set-quotient S {l})

  universal-map-set-quotient-hom-Eq-Rel :
    hom-Eq-Rel R S → set-quotient R → set-quotient S
  universal-map-set-quotient-hom-Eq-Rel =
    map-reflecting-map-Eq-Rel
      ( eq-rel-hom-Eq-Rel R S)
      ( universal-reflecting-map-set-quotient-hom-Eq-Rel)

  reflects-universal-map-set-quotient-hom-Eq-Rel :
    reflects-Eq-Rel
      ( eq-rel-hom-Eq-Rel R S)
      ( universal-map-set-quotient-hom-Eq-Rel)
  reflects-universal-map-set-quotient-hom-Eq-Rel =
    reflects-map-reflecting-map-Eq-Rel
      ( eq-rel-hom-Eq-Rel R S)
      ( universal-reflecting-map-set-quotient-hom-Eq-Rel)
```

## Properties

### The inclusion of the quotient `(X → A)/~` into `X → A/R` is an embedding

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (X : UU l1) {A : UU l2} (R : Eq-Rel l3 A)
  (Q : Set l4)
  (q : reflecting-map-Eq-Rel (eq-rel-function-type X R) (type-Set Q))
  (Uq : {l : Level} → is-set-quotient l (eq-rel-function-type X R) Q q)
  (QR : Set l5) (qR : reflecting-map-Eq-Rel R (type-Set QR))
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
      ( exponent-reflecting-map-Eq-Rel X R qR)
      ( λ g h p x →
        apply-effectiveness-is-set-quotient R QR qR UqR (htpy-eq p x))
```

### The extension of the universal map from `hom-Eq-Rel R S` to `A/R → B/S` to the quotient is an embedding

#### First variant using only the universal property of the set quotient

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  (QR : Set l3) (qR : reflecting-map-Eq-Rel R (type-Set QR))
  (UR : {l : Level} → is-set-quotient l R QR qR)
  {B : UU l4} (S : Eq-Rel l5 B)
  (QS : Set l6) (qS : reflecting-map-Eq-Rel S (type-Set QS))
  (US : {l : Level} → is-set-quotient l S QS qS)
  (QH : Set l7)
  (qH : reflecting-map-Eq-Rel (eq-rel-hom-Eq-Rel R S) (type-Set QH))
  (UH : {l : Level} → is-set-quotient l (eq-rel-hom-Eq-Rel R S) QH qH)
  where

  unique-inclusion-is-set-quotient-hom-Eq-Rel :
    is-contr
      ( Σ ( type-hom-Set QH (hom-Set QR QS))
          ( λ μ →
            ( μ ∘ map-reflecting-map-Eq-Rel (eq-rel-hom-Eq-Rel R S) qH) ~
            ( universal-map-is-set-quotient-hom-Eq-Rel R QR qR UR S QS qS US)))
  unique-inclusion-is-set-quotient-hom-Eq-Rel =
    universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Eq-Rel R S)
      ( QH)
      ( qH)
      ( UH)
      ( hom-Set QR QS)
      ( universal-reflecting-map-is-set-quotient-hom-Eq-Rel
        R QR qR UR S QS qS US)

  inclusion-is-set-quotient-hom-Eq-Rel :
    type-hom-Set QH (hom-Set QR QS)
  inclusion-is-set-quotient-hom-Eq-Rel =
    pr1 (center (unique-inclusion-is-set-quotient-hom-Eq-Rel))

  triangle-inclusion-is-set-quotient-hom-Eq-Rel :
    ( inclusion-is-set-quotient-hom-Eq-Rel ∘
      map-reflecting-map-Eq-Rel (eq-rel-hom-Eq-Rel R S) qH) ~
    ( universal-map-is-set-quotient-hom-Eq-Rel R QR qR UR S QS qS US)
  triangle-inclusion-is-set-quotient-hom-Eq-Rel =
    pr2 (center (unique-inclusion-is-set-quotient-hom-Eq-Rel))

  is-emb-inclusion-is-set-quotient-hom-Eq-Rel :
    is-emb inclusion-is-set-quotient-hom-Eq-Rel
  is-emb-inclusion-is-set-quotient-hom-Eq-Rel =
    is-emb-map-universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Eq-Rel R S)
      ( QH)
      ( qH)
      ( UH)
      ( hom-Set QR QS)
      ( universal-reflecting-map-is-set-quotient-hom-Eq-Rel
        R QR qR UR S QS qS US)
      ( λ g h p a →
        apply-effectiveness-is-set-quotient S QS qS US
          ( ( inv-htpy
              ( coherence-square-map-is-set-quotient R QR qR S QS qS UR US g) ∙h
              ( ( htpy-eq p ·r map-reflecting-map-Eq-Rel R qR) ∙h
                ( coherence-square-map-is-set-quotient
                  R QR qR S QS qS UR US h)))
            ( a)))

  emb-inclusion-is-set-quotient-hom-Eq-Rel :
    type-Set QH ↪ type-hom-Set QR QS
  pr1 emb-inclusion-is-set-quotient-hom-Eq-Rel =
    inclusion-is-set-quotient-hom-Eq-Rel
  pr2 emb-inclusion-is-set-quotient-hom-Eq-Rel =
    is-emb-inclusion-is-set-quotient-hom-Eq-Rel
```

#### Second variant using the official set quotients

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : UU l1} (R : Eq-Rel l2 A)
  {B : UU l3} (S : Eq-Rel l4 B)
  where

  quotient-hom-Eq-Rel-Set : Set (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  quotient-hom-Eq-Rel-Set = quotient-Set (eq-rel-hom-Eq-Rel R S)

  set-quotient-hom-Eq-Rel : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  set-quotient-hom-Eq-Rel = type-Set quotient-hom-Eq-Rel-Set

  is-set-set-quotient-hom-Eq-Rel : is-set set-quotient-hom-Eq-Rel
  is-set-set-quotient-hom-Eq-Rel = is-set-type-Set quotient-hom-Eq-Rel-Set

  reflecting-map-quotient-map-hom-Eq-Rel :
    reflecting-map-Eq-Rel (eq-rel-hom-Eq-Rel R S) set-quotient-hom-Eq-Rel
  reflecting-map-quotient-map-hom-Eq-Rel =
    reflecting-map-quotient-map (eq-rel-hom-Eq-Rel R S)

  quotient-map-hom-Eq-Rel : hom-Eq-Rel R S → set-quotient-hom-Eq-Rel
  quotient-map-hom-Eq-Rel = quotient-map (eq-rel-hom-Eq-Rel R S)

  is-set-quotient-set-quotient-hom-Eq-Rel :
    {l : Level} →
    is-set-quotient l
      ( eq-rel-hom-Eq-Rel R S)
      ( quotient-hom-Eq-Rel-Set)
      ( reflecting-map-quotient-map-hom-Eq-Rel)
  is-set-quotient-set-quotient-hom-Eq-Rel =
    is-set-quotient-set-quotient (eq-rel-hom-Eq-Rel R S)

  unique-inclusion-set-quotient-hom-Eq-Rel :
    is-contr
      ( Σ ( set-quotient-hom-Eq-Rel →
            set-quotient R → set-quotient S)
          ( λ μ →
            ( μ ∘ quotient-map (eq-rel-hom-Eq-Rel R S)) ~
            ( universal-map-set-quotient-hom-Eq-Rel R S)))
  unique-inclusion-set-quotient-hom-Eq-Rel =
    universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Eq-Rel R S)
      ( quotient-hom-Eq-Rel-Set)
      ( reflecting-map-quotient-map-hom-Eq-Rel)
      ( is-set-quotient-set-quotient-hom-Eq-Rel)
      ( hom-Set (quotient-Set R) (quotient-Set S))
      ( universal-reflecting-map-set-quotient-hom-Eq-Rel R S)

  inclusion-set-quotient-hom-Eq-Rel :
    set-quotient (eq-rel-hom-Eq-Rel R S) → set-quotient R → set-quotient S
  inclusion-set-quotient-hom-Eq-Rel =
    pr1 (center (unique-inclusion-set-quotient-hom-Eq-Rel))

  triangle-inclusion-set-quotient-hom-Eq-Rel :
    ( inclusion-set-quotient-hom-Eq-Rel ∘
      quotient-map (eq-rel-hom-Eq-Rel R S)) ~
    ( universal-map-set-quotient-hom-Eq-Rel R S)
  triangle-inclusion-set-quotient-hom-Eq-Rel =
    pr2 (center (unique-inclusion-set-quotient-hom-Eq-Rel))

  is-emb-inclusion-set-quotient-hom-Eq-Rel :
    is-emb inclusion-set-quotient-hom-Eq-Rel
  is-emb-inclusion-set-quotient-hom-Eq-Rel =
    is-emb-map-universal-property-set-quotient-is-set-quotient
      ( eq-rel-hom-Eq-Rel R S)
      ( quotient-hom-Eq-Rel-Set)
      ( reflecting-map-quotient-map-hom-Eq-Rel)
      ( is-set-quotient-set-quotient-hom-Eq-Rel)
      ( hom-Set (quotient-Set R) (quotient-Set S))
      ( universal-reflecting-map-set-quotient-hom-Eq-Rel R S)
      ( λ g h p a →
        apply-effectiveness-quotient-map S
          ( ( inv-htpy
              ( coherence-square-map-set-quotient R S g) ∙h
              ( ( htpy-eq p ·r quotient-map R) ∙h
                ( coherence-square-map-set-quotient
                  R S h)))
            ( a)))

  emb-inclusion-set-quotient-hom-Eq-Rel :
    set-quotient (eq-rel-hom-Eq-Rel R S) ↪ (set-quotient R → set-quotient S)
  pr1 emb-inclusion-set-quotient-hom-Eq-Rel =
    inclusion-set-quotient-hom-Eq-Rel
  pr2 emb-inclusion-set-quotient-hom-Eq-Rel =
    is-emb-inclusion-set-quotient-hom-Eq-Rel
```
