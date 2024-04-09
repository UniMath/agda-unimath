# Split idempotent maps

```agda
module foundation.split-idempotent-maps where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-higher-identifications-functions
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.fixed-points-endofunctions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-algebra
open import foundation.homotopy-induction
open import foundation.idempotent-maps
open import foundation.inverse-sequential-diagrams
open import foundation.path-algebra
open import foundation.quasicoherently-idempotent-maps
open import foundation.retracts-of-types
open import foundation.sequential-limits
open import foundation.structure-identity-principle
open import foundation.univalence
open import foundation.universe-levels
open import foundation.weakly-constant-maps
open import foundation.whiskering-homotopies-composition

open import foundation-core.commuting-squares-of-homotopies
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.sets
open import foundation-core.small-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A map `f : A → A` is
{{#concept "split idempotent" Agda=is-split-idempotent-map}} if there exists a
type `B` and an inclusion-retraction pair `i , r` displaying `B` as a
[retract](foundation-core.retracts-of-types.md) of `A`, and such that
`i ∘ r ~ f`. In other words, if we have a commutative diagram

```text
           f
       A ----> A
      ∧ \     ∧
   i /   \r  / i
    /     ∨ /
  B ====== B.
```

## Definitions

### The structure on a map of split idempotence

```agda
is-split-idempotent-map :
  {l1 : Level} (l2 : Level) {A : UU l1} → (A → A) → UU (l1 ⊔ lsuc l2)
is-split-idempotent-map l2 {A} f =
  Σ ( UU l2)
    ( λ B →
      Σ ( B retract-of A)
        ( λ R → inclusion-retract R ∘ map-retraction-retract R ~ f))

module _
  {l1 l2 : Level} {A : UU l1} {f : A → A} (H : is-split-idempotent-map l2 f)
  where

  splitting-type-is-split-idempotent-map : UU l2
  splitting-type-is-split-idempotent-map = pr1 H

  retract-is-split-idempotent-map :
    splitting-type-is-split-idempotent-map retract-of A
  retract-is-split-idempotent-map = pr1 (pr2 H)

  inclusion-is-split-idempotent-map : splitting-type-is-split-idempotent-map → A
  inclusion-is-split-idempotent-map =
    inclusion-retract retract-is-split-idempotent-map

  map-retraction-is-split-idempotent-map :
    A → splitting-type-is-split-idempotent-map
  map-retraction-is-split-idempotent-map =
    map-retraction-retract retract-is-split-idempotent-map

  retraction-is-split-idempotent-map :
    retraction inclusion-is-split-idempotent-map
  retraction-is-split-idempotent-map =
    retraction-retract retract-is-split-idempotent-map

  is-retraction-map-retraction-is-split-idempotent-map :
    is-retraction
      ( inclusion-is-split-idempotent-map)
      ( map-retraction-is-split-idempotent-map)
  is-retraction-map-retraction-is-split-idempotent-map =
    is-retraction-map-retraction-retract retract-is-split-idempotent-map

  htpy-is-split-idempotent-map :
    inclusion-is-split-idempotent-map ∘ map-retraction-is-split-idempotent-map ~
    f
  htpy-is-split-idempotent-map = pr2 (pr2 H)
```

### The type of split idempotent maps

```agda
split-idempotent-map : {l1 : Level} (l2 : Level) (A : UU l1) → UU (l1 ⊔ lsuc l2)
split-idempotent-map l2 A = Σ (A → A) (is-split-idempotent-map l2)

module _
  {l1 l2 : Level} {A : UU l1} (H : split-idempotent-map l2 A)
  where

  map-split-idempotent-map : A → A
  map-split-idempotent-map = pr1 H

  is-split-idempotent-split-idempotent-map :
    is-split-idempotent-map l2 map-split-idempotent-map
  is-split-idempotent-split-idempotent-map = pr2 H

  splitting-type-split-idempotent-map : UU l2
  splitting-type-split-idempotent-map =
    splitting-type-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map)

  retract-split-idempotent-map :
    splitting-type-split-idempotent-map retract-of A
  retract-split-idempotent-map =
    retract-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  inclusion-split-idempotent-map : splitting-type-split-idempotent-map → A
  inclusion-split-idempotent-map =
    inclusion-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  map-retraction-split-idempotent-map : A → splitting-type-split-idempotent-map
  map-retraction-split-idempotent-map =
    map-retraction-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map)

  retraction-split-idempotent-map : retraction inclusion-split-idempotent-map
  retraction-split-idempotent-map =
    retraction-is-split-idempotent-map is-split-idempotent-split-idempotent-map

  is-retraction-map-retraction-split-idempotent-map :
    is-retraction
      ( inclusion-split-idempotent-map)
      ( map-retraction-split-idempotent-map)
  is-retraction-map-retraction-split-idempotent-map =
    is-retraction-map-retraction-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map)

  htpy-split-idempotent-map :
    inclusion-split-idempotent-map ∘ map-retraction-split-idempotent-map ~
    map-split-idempotent-map
  htpy-split-idempotent-map =
    htpy-is-split-idempotent-map is-split-idempotent-split-idempotent-map
```

## Properties

### Split idempotence is closed under equivalences of splitting types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {f : A → A}
  (H : is-split-idempotent-map l3 f)
  (e : B ≃ splitting-type-is-split-idempotent-map H)
  where

  inclusion-is-split-idempotent-map-equiv-splitting-type : B → A
  inclusion-is-split-idempotent-map-equiv-splitting-type =
    inclusion-is-split-idempotent-map H ∘ map-equiv e

  map-retraction-is-split-idempotent-map-equiv-splitting-type : A → B
  map-retraction-is-split-idempotent-map-equiv-splitting-type =
    map-inv-equiv e ∘ map-retraction-is-split-idempotent-map H

  htpy-is-split-idempotent-map-equiv-splitting-type :
    inclusion-is-split-idempotent-map-equiv-splitting-type ∘
    map-retraction-is-split-idempotent-map-equiv-splitting-type ~
    f
  htpy-is-split-idempotent-map-equiv-splitting-type =
    ( double-whisker-comp
      ( inclusion-is-split-idempotent-map H)
      ( is-section-map-section-map-equiv e)
      ( map-retraction-is-split-idempotent-map H)) ∙h
    ( htpy-is-split-idempotent-map H)

  is-split-idempotent-map-equiv-splitting-type :
    is-split-idempotent-map l2 f
  is-split-idempotent-map-equiv-splitting-type =
    ( B ,
      comp-retract (retract-is-split-idempotent-map H) (retract-equiv e) ,
      htpy-is-split-idempotent-map-equiv-splitting-type)
```

### The splitting type of a split idempotent map is essentially unique

This is Lemma 3.4 in {{#cite Shu17}}. Note that it does not require any
postulates.

```agda
module _
  {l1 : Level} {A : UU l1} {f : A → A}
  where

  map-essentially-unique-splitting-type-is-split-idempotent-map :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    splitting-type-is-split-idempotent-map H →
    splitting-type-is-split-idempotent-map H'
  map-essentially-unique-splitting-type-is-split-idempotent-map H H' =
    map-retraction-is-split-idempotent-map H' ∘
    inclusion-is-split-idempotent-map H

  is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map' :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    is-section
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H H')
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H' H)
  is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map'
    H H' =
    ( map-retraction-is-split-idempotent-map H' ·l
      ( ( htpy-is-split-idempotent-map H) ∙h
        ( inv-htpy (htpy-is-split-idempotent-map H'))) ·r
      inclusion-is-split-idempotent-map H') ∙h
    ( horizontal-concat-htpy
      ( is-retraction-map-retraction-is-split-idempotent-map H')
      ( is-retraction-map-retraction-is-split-idempotent-map H'))

  is-equiv-map-essentially-unique-splitting-type-is-split-idempotent-map :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    is-equiv
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H H')
  is-equiv-map-essentially-unique-splitting-type-is-split-idempotent-map H H' =
    is-equiv-is-invertible
      ( map-essentially-unique-splitting-type-is-split-idempotent-map H' H)
      ( is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map'
        ( H)
        ( H'))
      ( is-fibered-involution-essentially-unique-splitting-type-is-split-idempotent-map'
        ( H')
        ( H))

  essentially-unique-splitting-type-is-split-idempotent-map :
    {l2 l3 : Level}
    (H : is-split-idempotent-map l2 f)
    (H' : is-split-idempotent-map l3 f) →
    splitting-type-is-split-idempotent-map H ≃
    splitting-type-is-split-idempotent-map H'
  essentially-unique-splitting-type-is-split-idempotent-map H H' =
    ( map-essentially-unique-splitting-type-is-split-idempotent-map H H' ,
      is-equiv-map-essentially-unique-splitting-type-is-split-idempotent-map
        ( H)
        ( H'))
```

### Characterizing equality of split idempotence structures

```agda
module _
  {l1 l2 : Level} {A : UU l1} {f : A → A}
  where

  coherence-equiv-is-split-idempotent-map :
    {l3 : Level}
    (R : is-split-idempotent-map l2 f)
    (S : is-split-idempotent-map l3 f) →
    (e :
      splitting-type-is-split-idempotent-map R ≃
      splitting-type-is-split-idempotent-map S)
    ( H :
      htpy-retract
        ( retract-is-split-idempotent-map R)
        ( comp-retract (retract-is-split-idempotent-map S) (retract-equiv e))) →
    UU l1
  coherence-equiv-is-split-idempotent-map R S e H =
    htpy-is-split-idempotent-map R ~
    horizontal-concat-htpy (pr1 H) (pr1 (pr2 H)) ∙h
    htpy-is-split-idempotent-map-equiv-splitting-type S e

  equiv-is-split-idempotent-map :
    {l3 : Level}
    (R : is-split-idempotent-map l2 f)
    (S : is-split-idempotent-map l3 f) →
    UU (l1 ⊔ l2 ⊔ l3)
  equiv-is-split-idempotent-map R S =
    Σ ( splitting-type-is-split-idempotent-map R ≃
        splitting-type-is-split-idempotent-map S)
      ( λ e →
        Σ ( htpy-retract
            ( retract-is-split-idempotent-map R)
            ( comp-retract
              ( retract-is-split-idempotent-map S)
              ( retract-equiv e)))
          ( coherence-equiv-is-split-idempotent-map R S e))

  id-equiv-is-split-idempotent-map :
    (R : is-split-idempotent-map l2 f) → equiv-is-split-idempotent-map R R
  id-equiv-is-split-idempotent-map R =
    ( ( id-equiv) ,
      ( refl-htpy ,
        refl-htpy ,
        ( inv-htpy
          ( left-unit-law-left-whisker-comp
            ( is-retraction-map-retraction-is-split-idempotent-map R)) ∙h
          inv-htpy-right-unit-htpy)) ,
      ( refl-htpy))

  equiv-eq-is-split-idempotent-map :
    (R S : is-split-idempotent-map l2 f) →
    R ＝ S → equiv-is-split-idempotent-map R S
  equiv-eq-is-split-idempotent-map R .R refl =
    id-equiv-is-split-idempotent-map R

  abstract
    is-torsorial-equiv-is-split-idempotent-map :
      (R : is-split-idempotent-map l2 f) →
      is-torsorial (equiv-is-split-idempotent-map {l2} R)
    is-torsorial-equiv-is-split-idempotent-map R =
      is-torsorial-Eq-structure
        ( is-torsorial-equiv (splitting-type-is-split-idempotent-map R))
        ( splitting-type-is-split-idempotent-map R , id-equiv)
        ( is-torsorial-Eq-structure
          ( is-contr-equiv
            ( Σ ( (splitting-type-is-split-idempotent-map R) retract-of A)
                ( htpy-retract (retract-is-split-idempotent-map R)))
            ( equiv-tot
              ( λ S →
                equiv-tot
                  ( λ I →
                    equiv-tot
                    ( λ J →
                      equiv-concat-htpy'
                        ( is-retraction-map-retraction-is-split-idempotent-map
                          ( R))
                        ( ap-concat-htpy
                          ( horizontal-concat-htpy J I)
                          ( right-unit-htpy ∙h
                            left-unit-law-left-whisker-comp
                              ( is-retraction-map-retraction-retract S)))))))
            ( is-torsorial-htpy-retract (retract-is-split-idempotent-map R)))
          ( ( retract-is-split-idempotent-map R) ,
            ( ( refl-htpy) ,
              ( refl-htpy) ,
              ( inv-htpy
                ( left-unit-law-left-whisker-comp
                  ( is-retraction-map-retraction-is-split-idempotent-map R)) ∙h
              inv-htpy-right-unit-htpy)))
          ( is-torsorial-htpy (htpy-is-split-idempotent-map R)))

  is-equiv-equiv-eq-is-split-idempotent-map :
    (R S : is-split-idempotent-map l2 f) →
    is-equiv (equiv-eq-is-split-idempotent-map R S)
  is-equiv-equiv-eq-is-split-idempotent-map R =
    fundamental-theorem-id
      ( is-torsorial-equiv-is-split-idempotent-map R)
      ( equiv-eq-is-split-idempotent-map R)

  equiv-equiv-eq-is-split-idempotent-map :
    (R S : is-split-idempotent-map l2 f) →
    (R ＝ S) ≃ equiv-is-split-idempotent-map R S
  equiv-equiv-eq-is-split-idempotent-map R S =
    ( equiv-eq-is-split-idempotent-map R S ,
      is-equiv-equiv-eq-is-split-idempotent-map R S)

  eq-equiv-is-split-idempotent-map :
    (R S : is-split-idempotent-map l2 f) →
    equiv-is-split-idempotent-map R S → R ＝ S
  eq-equiv-is-split-idempotent-map R S =
    map-inv-is-equiv (is-equiv-equiv-eq-is-split-idempotent-map R S)
```

### Split idempotent maps are idempotent

This is Lemma 3.3 in {{#cite Shu17}}.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {f : A → A} (H : is-split-idempotent-map l2 f)
  where

  is-idempotent-is-split-idempotent-map : is-idempotent-map f
  is-idempotent-is-split-idempotent-map =
    is-idempotent-map-inv-htpy
      ( is-idempotent-inclusion-retraction
        ( inclusion-is-split-idempotent-map H)
        ( map-retraction-is-split-idempotent-map H)
        ( is-retraction-map-retraction-is-split-idempotent-map H))
      ( htpy-is-split-idempotent-map H)

module _
  {l1 l2 : Level} {A : UU l1} (H : split-idempotent-map l2 A)
  where

  is-idempotent-split-idempotent-map :
    is-idempotent-map (map-split-idempotent-map H)
  is-idempotent-split-idempotent-map =
    is-idempotent-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map H)
```

### Split idempotent maps are quasicoherently idempotent

This is Lemma 3.6 in {{#cite Shu17}}. We follow a more direct route as we have
already shown that quasicoherently idempotents are closed under homotopy.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {f : A → A} (H : is-split-idempotent-map l2 f)
  where

  abstract
    coherence-is-quasicoherently-idempotent-is-split-idempotent-map :
      coherence-is-quasicoherently-idempotent-map f
        ( is-idempotent-is-split-idempotent-map H)
    coherence-is-quasicoherently-idempotent-is-split-idempotent-map =
      coherence-is-quasicoherently-idempotent-is-idempotent-map-htpy
        ( is-quasicoherently-idempotent-map-inv-htpy
          ( is-quasicoherently-idempotent-inclusion-retraction
            ( inclusion-is-split-idempotent-map H)
            ( map-retraction-is-split-idempotent-map H)
            (is-retraction-map-retraction-is-split-idempotent-map H))
          ( htpy-is-split-idempotent-map H))
        ( is-idempotent-is-split-idempotent-map H)
        ( ap-concat-htpy _ (inv-inv-htpy (htpy-is-split-idempotent-map H)))

  is-quasicoherently-idempotent-is-split-idempotent-map :
    is-quasicoherently-idempotent-map f
  is-quasicoherently-idempotent-is-split-idempotent-map =
    ( is-idempotent-is-split-idempotent-map H ,
      coherence-is-quasicoherently-idempotent-is-split-idempotent-map)

module _
  {l1 l2 : Level} {A : UU l1} (H : split-idempotent-map l2 A)
  where

  is-quasicoherently-idempotent-split-idempotent-map :
    is-quasicoherently-idempotent-map (map-split-idempotent-map H)
  is-quasicoherently-idempotent-split-idempotent-map =
    is-quasicoherently-idempotent-is-split-idempotent-map
      ( is-split-idempotent-split-idempotent-map H)
```

### Every idempotent on a set splits

This is Theorem 3.7 of {{#cite Shu17}}.

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (is-set-A : is-set A) (H : is-idempotent-map f)
  where

  splitting-type-is-split-idempotent-is-idempotent-map-is-set : UU l
  splitting-type-is-split-idempotent-is-idempotent-map-is-set =
    fixed-point f

  inclusion-is-split-idempotent-is-idempotent-map-is-set :
    splitting-type-is-split-idempotent-is-idempotent-map-is-set → A
  inclusion-is-split-idempotent-is-idempotent-map-is-set = pr1

  map-retraction-is-split-idempotent-is-idempotent-map-is-set :
    A → splitting-type-is-split-idempotent-is-idempotent-map-is-set
  map-retraction-is-split-idempotent-is-idempotent-map-is-set x = (f x , H x)

  is-retraction-map-retraction-is-split-idempotent-is-idempotent-map-is-set :
    is-retraction
      ( inclusion-is-split-idempotent-is-idempotent-map-is-set)
      ( map-retraction-is-split-idempotent-is-idempotent-map-is-set)
  is-retraction-map-retraction-is-split-idempotent-is-idempotent-map-is-set
    (x , p) =
    eq-pair-Σ p (eq-is-prop (is-set-A (f x) x))

  retraction-is-split-idempotent-is-idempotent-map-is-set :
    retraction (inclusion-is-split-idempotent-is-idempotent-map-is-set)
  retraction-is-split-idempotent-is-idempotent-map-is-set =
    ( map-retraction-is-split-idempotent-is-idempotent-map-is-set ,
      is-retraction-map-retraction-is-split-idempotent-is-idempotent-map-is-set)

  retract-is-split-idempotent-is-idempotent-map-is-set :
    splitting-type-is-split-idempotent-is-idempotent-map-is-set retract-of A
  retract-is-split-idempotent-is-idempotent-map-is-set =
    ( inclusion-is-split-idempotent-is-idempotent-map-is-set ,
      retraction-is-split-idempotent-is-idempotent-map-is-set)

  htpy-is-split-idempotent-is-idempotent-map-is-set :
    inclusion-is-split-idempotent-is-idempotent-map-is-set ∘
    map-retraction-is-split-idempotent-is-idempotent-map-is-set ~
    f
  htpy-is-split-idempotent-is-idempotent-map-is-set = refl-htpy

  is-split-idempotent-is-idempotent-map-is-set : is-split-idempotent-map l f
  is-split-idempotent-is-idempotent-map-is-set =
    ( splitting-type-is-split-idempotent-is-idempotent-map-is-set ,
      retract-is-split-idempotent-is-idempotent-map-is-set ,
      htpy-is-split-idempotent-is-idempotent-map-is-set)
```

### Weakly constant idempotent maps split

This is Theorem 3.9 of {{#cite Shu17}}.

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (H : is-idempotent-map f) (W : is-weakly-constant-map f)
  where

  splitting-type-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    UU l
  splitting-type-is-split-idempotent-is-weakly-constant-is-idempotent-map =
    fixed-point f

  inclusion-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    splitting-type-is-split-idempotent-is-weakly-constant-is-idempotent-map →
    A
  inclusion-is-split-idempotent-is-weakly-constant-is-idempotent-map = pr1

  map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    A →
    splitting-type-is-split-idempotent-is-weakly-constant-is-idempotent-map
  map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map x =
    ( f x , H x)

  is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    is-retraction
      ( inclusion-is-split-idempotent-is-weakly-constant-is-idempotent-map)
      ( map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map)
  is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map
    _ =
    eq-is-prop (is-prop-fixed-point-is-weakly-constant-map W)

  retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    retraction
      ( inclusion-is-split-idempotent-is-weakly-constant-is-idempotent-map)
  retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map =
    ( map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map ,
      is-retraction-map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map)

  retract-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    retract
      ( A)
      ( splitting-type-is-split-idempotent-is-weakly-constant-is-idempotent-map)
  retract-is-split-idempotent-is-weakly-constant-is-idempotent-map =
    ( inclusion-is-split-idempotent-is-weakly-constant-is-idempotent-map ,
      retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map)

  htpy-is-split-idempotent-is-weakly-constant-is-idempotent-map :
    inclusion-is-split-idempotent-is-weakly-constant-is-idempotent-map ∘
    map-retraction-is-split-idempotent-is-weakly-constant-is-idempotent-map ~
    f
  htpy-is-split-idempotent-is-weakly-constant-is-idempotent-map = refl-htpy

  is-split-idempotent-is-weakly-constant-is-idempotent-map :
    is-split-idempotent-map l f
  is-split-idempotent-is-weakly-constant-is-idempotent-map =
    ( splitting-type-is-split-idempotent-is-weakly-constant-is-idempotent-map ,
      retract-is-split-idempotent-is-weakly-constant-is-idempotent-map ,
      htpy-is-split-idempotent-is-weakly-constant-is-idempotent-map)
```

### Quasicoherently idempotent maps split

This is Theorem 5.3 of {{#cite Shu17}}.

As per Remark 5.4 {{#cite Shu17}}, the inclusion of `A` into the splitting type
can be constructed for any endofunction `f`.

```agda
module _
  {l : Level} {A : UU l} (f : A → A)
  where

  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map' :
    inverse-sequential-diagram l
  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map' =
    ( (λ _ → A) , (λ _ → f))

  splitting-type-is-quasicoherently-idempotent-map' : UU l
  splitting-type-is-quasicoherently-idempotent-map' =
    standard-sequential-limit
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map')

  inclusion-splitting-type-is-quasicoherently-idempotent-map' :
    splitting-type-is-quasicoherently-idempotent-map' → A
  inclusion-splitting-type-is-quasicoherently-idempotent-map' (a , α) = a 0
```

Moreover, again by Remark 5.4 {{#cite Shu17}}, given the idempotence homotopy
`f ∘ f ~ f`, we can construct the converse map to this inclusion and show that
this gives a factorization of `f`. Indeed, this factorization is strict.

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (I : is-idempotent-map f)
  where

  map-retraction-splitting-type-is-quasicoherently-idempotent-map' :
    A → splitting-type-is-quasicoherently-idempotent-map' f
  map-retraction-splitting-type-is-quasicoherently-idempotent-map' x =
    ( (λ _ → f x) , (λ _ → inv (I x)))

  htpy-is-split-idempotent-is-quasicoherently-idempotent-map' :
    inclusion-splitting-type-is-quasicoherently-idempotent-map' f ∘
    map-retraction-splitting-type-is-quasicoherently-idempotent-map' ~
    f
  htpy-is-split-idempotent-is-quasicoherently-idempotent-map' = refl-htpy
```

To show that these maps form an inclusion-retraction pair, however, we use the
coherence of quasicoherently idempotents as well as
[function extensionality](foundation.function-extensionality.md).

```agda
module _
  {l : Level} {A : UU l} {f : A → A}
  (H : is-quasicoherently-idempotent-map f)
  where

  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map :
    inverse-sequential-diagram l
  inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map =
    inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map'
      ( f)

  splitting-type-is-quasicoherently-idempotent-map : UU l
  splitting-type-is-quasicoherently-idempotent-map =
    splitting-type-is-quasicoherently-idempotent-map' f

  inclusion-splitting-type-is-quasicoherently-idempotent-map :
    splitting-type-is-quasicoherently-idempotent-map → A
  inclusion-splitting-type-is-quasicoherently-idempotent-map =
    inclusion-splitting-type-is-quasicoherently-idempotent-map' f

  map-retraction-splitting-type-is-quasicoherently-idempotent-map :
    A → splitting-type-is-quasicoherently-idempotent-map
  map-retraction-splitting-type-is-quasicoherently-idempotent-map =
    map-retraction-splitting-type-is-quasicoherently-idempotent-map'
      ( is-idempotent-is-quasicoherently-idempotent-map H)

  htpy-is-split-idempotent-is-quasicoherently-idempotent-map :
    inclusion-splitting-type-is-quasicoherently-idempotent-map ∘
    map-retraction-splitting-type-is-quasicoherently-idempotent-map ~
    f
  htpy-is-split-idempotent-is-quasicoherently-idempotent-map =
    htpy-is-split-idempotent-is-quasicoherently-idempotent-map'
      ( is-idempotent-is-quasicoherently-idempotent-map H)
```

Now, to construct the desired retracting homotopy

```text
  r ∘ i ~ id
```

we subdivide the problem into two. First, we show that shifting the sequence and
whiskering by `f ∘ f` is homotopic to the identity

```text
  ((f (f a₍₋₎₊₁)) , (f ∘ f) ·l α₍₋₎₊₁) ~ (a , α).
```

```agda
  shift-retraction-splitting-type-is-quasicoherently-idempotent-map :
    standard-sequential-limit
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map) →
    standard-sequential-limit
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)
  shift-retraction-splitting-type-is-quasicoherently-idempotent-map (a , α) =
    ((f ∘ f ∘ a ∘ succ-ℕ) , ( (f ∘ f) ·l (α ∘ succ-ℕ)))

  htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map :
    ((a , α) :
      standard-sequential-limit
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)) →
    f ∘ f ∘ a ∘ succ-ℕ ~ a
  htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map
    ( a , α) n =
    is-idempotent-is-quasicoherently-idempotent-map H (a (succ-ℕ n)) ∙ inv (α n)

  abstract
    htpy-coherence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map :
      (x :
        standard-sequential-limit
          ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)) →
      coherence-Eq-standard-sequential-limit
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)
        ( shift-retraction-splitting-type-is-quasicoherently-idempotent-map x)
        ( x)
        ( htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map
          ( x))
    htpy-coherence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map
      ( a , α) n =
      ( ap
        ( ap (f ∘ f) (α (succ-ℕ n)) ∙_)
        ( ( ap-concat f
            ( is-idempotent-is-quasicoherently-idempotent-map H
              ( a (second-succ-ℕ n)))
            ( inv (α (succ-ℕ n)))) ∙
          ( ap
            ( _∙ ap f (inv (α (succ-ℕ n))))
            ( coh-is-quasicoherently-idempotent-map H
              ( a (second-succ-ℕ n)))))) ∙
      ( inv
        ( assoc
          ( ap (f ∘ f) (α (succ-ℕ n)))
          ( is-idempotent-is-quasicoherently-idempotent-map H
            ( f (a (second-succ-ℕ n))))
          ( ap f (inv (α (succ-ℕ n)))))) ∙
      ( ap
        ( _∙ ap f (inv (α (succ-ℕ n))))
        ( inv
          ( nat-htpy
            ( is-idempotent-is-quasicoherently-idempotent-map H)
            ( α (succ-ℕ n))))) ∙
      ( assoc
        ( is-idempotent-is-quasicoherently-idempotent-map H (a (succ-ℕ n)))
        ( ap f (α (succ-ℕ n)))
        ( ap f (inv (α (succ-ℕ n))))) ∙
      ( ap
        ( is-idempotent-is-quasicoherently-idempotent-map H (a (succ-ℕ n)) ∙_)
        ( ( inv (ap-concat f (α (succ-ℕ n)) (inv (α (succ-ℕ n))))) ∙
          ( ap² f (right-inv (α (succ-ℕ n)))) ∙
          inv (left-inv (α n)))) ∙
      ( inv
        ( assoc
          ( is-idempotent-is-quasicoherently-idempotent-map H (a (succ-ℕ n)))
          ( inv (α n))
          ( α n)))

  compute-shift-retraction-splitting-type-is-quasicoherently-idempotent-map :
    shift-retraction-splitting-type-is-quasicoherently-idempotent-map ~ id
  compute-shift-retraction-splitting-type-is-quasicoherently-idempotent-map
    x =
    eq-Eq-standard-sequential-limit
      ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)
      ( shift-retraction-splitting-type-is-quasicoherently-idempotent-map x)
      ( x)
      ( ( htpy-sequence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map
          x) ,
        ( htpy-coherence-shift-retraction-splitting-type-is-quasicoherently-idempotent-map
          x))
```

Then we show that `r ∘ i` is homotopic to this operation. This time we proceed
by induction on `n`.

```agda
  htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map :
    ( (a , α) :
      standard-sequential-limit
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map'
          ( f))) →
    ( λ _ →
      f (inclusion-splitting-type-is-quasicoherently-idempotent-map (a , α))) ~
    ( f ∘ f ∘ a ∘ succ-ℕ)
  htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
    ( a , α) 0 = ap f (α 0)
  htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
    ( a , α) (succ-ℕ n) =
    ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
      ( a , α) n) ∙
    ( is-idempotent-is-quasicoherently-idempotent-map H (a (succ-ℕ n))) ∙
    ( ap f (α (succ-ℕ n)))

  abstract
    htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map :
      ((a , α) :
        standard-sequential-limit
          ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)) →
      coherence-square-homotopies
        ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
          ( a , α))
        ( λ n →
          inv
            ( is-idempotent-is-quasicoherently-idempotent-map H
              ( inclusion-splitting-type-is-quasicoherently-idempotent-map
                ( a , α))))
        ( λ n → ap (f ∘ f) (α (succ-ℕ n)))
        ( λ n →
          ap f
            ( ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
                ( a , α)
                ( n)) ∙
              ( is-idempotent-is-quasicoherently-idempotent-map H
                ( a (succ-ℕ n))) ∙
              ( ap f (α (succ-ℕ n)))))
    htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
      ( a , α) 0 =
      ( ap
        ( inv (is-idempotent-is-quasicoherently-idempotent-map H (a 0)) ∙_)
        ( ( ap-concat f
            ( ap f (α 0) ∙
              is-idempotent-is-quasicoherently-idempotent-map H (a 1))
            ( ap f (α 1))) ∙
          ( ap-binary (_∙_)
            ( ap-concat f
              ( ap f (α 0))
              ( is-idempotent-is-quasicoherently-idempotent-map H (a 1)))
            ( inv (ap-comp f f (α 1)))))) ∙
      ( inv
          ( assoc
            ( inv (is-idempotent-is-quasicoherently-idempotent-map H (a 0)))
            ( ap f (ap f (α 0)) ∙
              ap f (is-idempotent-is-quasicoherently-idempotent-map H (a 1)))
            ( ap (f ∘ f) (α 1)))) ∙
      ( ap
        ( _∙ ap (f ∘ f) (α 1))
        ( ap
          ( inv (is-idempotent-is-quasicoherently-idempotent-map H (a 0)) ∙_)
          ( ( ap-binary (_∙_)
              ( inv (ap-comp f f (α 0)))
              ( coh-is-quasicoherently-idempotent-map H (a 1))) ∙
            ( inv
              ( nat-htpy
                ( is-idempotent-is-quasicoherently-idempotent-map H) (α 0)))) ∙
          ( left-left-inv
            ( is-idempotent-is-quasicoherently-idempotent-map H (a 0))
            ( ap f (α 0)))))
```

For the inductive step we fill the following diagram as prescribed, in the
notation of {{#cite Shu17}}:

```text
              ξₙ₊₁               I aₙ₊₁             f (αₙ₊₁)⁻¹
    f a₀ ------------> f (f aₙ₊₁) ---> f aₙ₊₁ --------------------> f (f aₙ₊₂)
     |                    |                  [nat-htpy]  ___ refl__/   |
  (I⁻¹ a₀)    [Ξₙ]        |       I (f aₙ₊₂)            /         (f ∘ f)(αₙ₊₂)
     ∨                    ∨        ------->           /                ∨
  f (f a₀) --------> f (f (f aₙ₊₂))   [J]   f (f aₙ₊₂) ----------> f (f (f aₙ₊₃))
     (f (ξₙ ∙ I aₙ₊₁ ∙ f αₙ₊₁))     ------->          (f ∘ f) (αₙ₊₂)
                                  f (I aₙ₊₂)
```

where the symbols translate to code as follows:

```text
I = is-idempotent-is-quasicoherently-idempotent-map H
J = coh-is-quasicoherently-idempotent-map H
ξ = htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map (a , α)
Ξ = htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map (a , α).
```

In particular, the left-hand square is the inductive hypothesis.

```agda
    htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
      ( a , α) (succ-ℕ n) =
      ( ap
        ( inv (I (a 0)) ∙_)
        ( ( ap-concat f
            ( ξ (succ-ℕ n) ∙ I (a (second-succ-ℕ n)))
            ( ap f (α (second-succ-ℕ n)))) ∙
          ( ap-binary (_∙_)
            ( ap-concat f (ξ (succ-ℕ n)) (I (a (second-succ-ℕ n))))
            ( inv (ap-comp f f (α (second-succ-ℕ n))))))) ∙
      ( inv
        ( assoc
          ( inv (I (a 0)))
          ( ap f
            ( ξ n ∙
              I (a (succ-ℕ n)) ∙
              ap f (α (succ-ℕ n))) ∙
              ap f (I (a (second-succ-ℕ n))))
          ( ap (f ∘ f) (α (second-succ-ℕ n))))) ∙
      ( ap
        ( _∙ ap (f ∘ f) (α (second-succ-ℕ n)))
        ( ( inv
            ( assoc
              ( inv (I (a 0)))
              ( ap f (ξ n ∙ I (a (succ-ℕ n)) ∙ ap f (α (succ-ℕ n))))
              ( ap f (I (a (second-succ-ℕ n)))))) ∙
          ( ap
            ( _∙ ap f (I ( a (second-succ-ℕ n))))
            ( htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
              ( a , α)
              ( n))) ∙
          ( assoc
              ( ξ n)
              ( ap (f ∘ f) (α (succ-ℕ n)))
              ( ap f (I (a (second-succ-ℕ n))))) ∙
          ( ap
            ( ξ n ∙_)
            ( ap
              ( ap (f ∘ f) (α (succ-ℕ n)) ∙_)
              ( coh-is-quasicoherently-idempotent-map H
                ( a (succ-ℕ (succ-ℕ n)))) ∙
            ( inv (nat-htpy I (α (succ-ℕ n)))))) ∙
          ( inv (assoc (ξ n) (I (a (succ-ℕ n))) (ap f (α (succ-ℕ n)))))))
      where
        ξ :
          ( λ _ →
            f ( inclusion-splitting-type-is-quasicoherently-idempotent-map
                ( a , α))) ~
          ( f ∘ f ∘ a ∘ succ-ℕ)
        ξ =
          htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
            ( a , α)
        I : is-idempotent-map f
        I = pr1 H

  abstract
    compute-retraction-splitting-type-is-quasicoherently-idempotent-map :
      map-retraction-splitting-type-is-quasicoherently-idempotent-map ∘
      inclusion-splitting-type-is-quasicoherently-idempotent-map ~
      shift-retraction-splitting-type-is-quasicoherently-idempotent-map
    compute-retraction-splitting-type-is-quasicoherently-idempotent-map
      x =
      eq-Eq-standard-sequential-limit
        ( inverse-sequential-diagram-splitting-type-is-quasicoherently-idempotent-map)
        ( map-retraction-splitting-type-is-quasicoherently-idempotent-map
          ( inclusion-splitting-type-is-quasicoherently-idempotent-map x))
        ( shift-retraction-splitting-type-is-quasicoherently-idempotent-map
          ( x))
        ( htpy-sequence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
            ( x) ,
          htpy-coherence-compute-retraction-splitting-type-is-quasicoherently-idempotent-map
            ( x))

  is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotent-map :
    is-retraction
      ( inclusion-splitting-type-is-quasicoherently-idempotent-map)
      ( map-retraction-splitting-type-is-quasicoherently-idempotent-map)
  is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotent-map =
    compute-retraction-splitting-type-is-quasicoherently-idempotent-map ∙h
    compute-shift-retraction-splitting-type-is-quasicoherently-idempotent-map

  retraction-splitting-type-is-quasicoherently-idempotent-map :
    retraction (inclusion-splitting-type-is-quasicoherently-idempotent-map)
  retraction-splitting-type-is-quasicoherently-idempotent-map =
    ( map-retraction-splitting-type-is-quasicoherently-idempotent-map ,
      is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotent-map)

  retract-splitting-type-is-quasicoherently-idempotent-map :
    splitting-type-is-quasicoherently-idempotent-map retract-of A
  retract-splitting-type-is-quasicoherently-idempotent-map =
    ( inclusion-splitting-type-is-quasicoherently-idempotent-map ,
      retraction-splitting-type-is-quasicoherently-idempotent-map)

  splitting-is-quasicoherently-idempotent-map : retracts l A
  splitting-is-quasicoherently-idempotent-map =
    ( splitting-type-is-quasicoherently-idempotent-map ,
      retract-splitting-type-is-quasicoherently-idempotent-map)

  is-split-idempotent-is-quasicoherently-idempotent-map :
    is-split-idempotent-map l f
  is-split-idempotent-is-quasicoherently-idempotent-map =
    ( splitting-type-is-quasicoherently-idempotent-map ,
      retract-splitting-type-is-quasicoherently-idempotent-map ,
      htpy-is-split-idempotent-is-quasicoherently-idempotent-map)
```

We record these same facts for the bundled data of a quasicoherently idempotent
map on `A`.

```agda
module _
  {l : Level} {A : UU l} (f : quasicoherently-idempotent-map A)
  where

  splitting-type-quasicoherently-idempotent-map : UU l
  splitting-type-quasicoherently-idempotent-map =
    splitting-type-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  inclusion-splitting-type-quasicoherently-idempotent-map :
    splitting-type-quasicoherently-idempotent-map → A
  inclusion-splitting-type-quasicoherently-idempotent-map =
    inclusion-splitting-type-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  map-retraction-splitting-type-quasicoherently-idempotent-map :
    A → splitting-type-quasicoherently-idempotent-map
  map-retraction-splitting-type-quasicoherently-idempotent-map =
    map-retraction-splitting-type-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  is-retraction-map-retraction-splitting-type-quasicoherently-idempotent-map :
    is-retraction
      ( inclusion-splitting-type-quasicoherently-idempotent-map)
      ( map-retraction-splitting-type-quasicoherently-idempotent-map)
  is-retraction-map-retraction-splitting-type-quasicoherently-idempotent-map =
    is-retraction-map-retraction-splitting-type-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  retraction-splitting-type-quasicoherently-idempotent-map :
    retraction (inclusion-splitting-type-quasicoherently-idempotent-map)
  retraction-splitting-type-quasicoherently-idempotent-map =
    retraction-splitting-type-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  retract-splitting-type-quasicoherently-idempotent-map :
    splitting-type-quasicoherently-idempotent-map retract-of A
  retract-splitting-type-quasicoherently-idempotent-map =
    retract-splitting-type-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  splitting-quasicoherently-idempotent-map : retracts l A
  splitting-quasicoherently-idempotent-map =
    splitting-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  htpy-is-split-idempotent-quasicoherently-idempotent-map :
    inclusion-splitting-type-quasicoherently-idempotent-map ∘
    map-retraction-splitting-type-quasicoherently-idempotent-map ~
    map-quasicoherently-idempotent-map f
  htpy-is-split-idempotent-quasicoherently-idempotent-map =
    htpy-is-split-idempotent-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)

  is-split-idempotent-quasicoherently-idempotent-map :
    is-split-idempotent-map l (map-quasicoherently-idempotent-map f)
  is-split-idempotent-quasicoherently-idempotent-map =
    is-split-idempotent-is-quasicoherently-idempotent-map
      ( is-quasicoherently-idempotent-quasicoherently-idempotent-map f)
```

### Small types are closed under retracts

<!-- TODO: move this somewhere more fitting. Currently moving it to foundation.small-types introduces cyclic dependencies -->

This is Theorem 2.13 of {{#cite dJE23}}. Note in particular that it does not
rely on univalence.

**Proof:** Given an inclusion-retraction pair `i , r` that displays `B` as a
retract of `A` where `A` is a small type, then we have two candidates for the
splitting type of `i ∘ r`, the first is `B` and the other is the splitting type
constructed for

```text
  is-split-idempotent-is-quasicoherently-idempotent-map
    ( is-quasicoherently-idempotent-inclusion-retraction i r ...).
```

The latter is a small sequential limit, and by essential uniqueness of splitting
types they are equivalent so we are done.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-small-retract' : B retract-of A → is-small l1 B
  pr1 (is-small-retract' R) =
    splitting-type-is-quasicoherently-idempotent-map'
      ( inclusion-retract R ∘ map-retraction-retract R)
  pr2 (is-small-retract' R) =
    essentially-unique-splitting-type-is-split-idempotent-map
      ( B , R , refl-htpy)
      ( is-split-idempotent-is-quasicoherently-idempotent-map
        ( is-quasicoherently-idempotent-inclusion-retraction
          ( inclusion-retract R)
          ( map-retraction-retract R)
          ( is-retraction-map-retraction-retract R)))

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2}
  where

  is-small-retract : is-small l3 A → B retract-of A → is-small l3 B
  is-small-retract is-small-A r =
    is-small-retract'
      ( comp-retract (retract-equiv (equiv-is-small is-small-A)) r)
```

## References

{{#bibliography}} {{#reference Shu17}} {{#reference Shu14SplittingIdempotents}}
