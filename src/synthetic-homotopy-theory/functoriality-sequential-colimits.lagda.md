# Functoriality of sequential colimits

```agda
module synthetic-homotopy-theory.functoriality-sequential-colimits where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-prisms-of-maps
open import foundation.commuting-squares-of-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-colimits
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Idea

A
[morphism of sequential diagrams](synthetic-homotopy-theory.morphisms-sequential-diagrams.md)
`f : (A, a) → (B, b)` induces a map `f∞ : A∞ → B∞` between the
[standard sequential colimits](synthetic-homotopy-theory.sequential-colimits.md)
of the diagrams.

## Properties

### A morphism of sequential diagrams induces a map of cocones

```agda
module _
  { l1 l2 l3 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( f : hom-sequential-diagram A B) {X : UU l3}
  where

  map-hom-cocone-sequential-colimit :
    cocone-sequential-diagram B X → cocone-sequential-diagram A X
  map-hom-cocone-sequential-colimit c =
    comp-hom-sequential-diagram A B
      ( constant-sequential-diagram X)
      ( c)
      ( f)
```

### A morphism of sequential diagrams induces a map of sequential colimits

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} (B : sequential-diagram l2)
  ( f : hom-sequential-diagram A B)
  where

  map-hom-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-hom-standard-sequential-colimit =
    map-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
      ( up-standard-sequential-colimit A)
      ( map-hom-cocone-sequential-colimit f
        ( cocone-standard-sequential-colimit B))

  htpy-cocone-map-hom-standard-sequential-colimit :
    htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram A
        ( cocone-standard-sequential-colimit A)
        ( map-hom-standard-sequential-colimit))
      ( map-hom-cocone-sequential-colimit f
        ( cocone-standard-sequential-colimit B))
  htpy-cocone-map-hom-standard-sequential-colimit =
    htpy-cocone-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
      ( up-standard-sequential-colimit A)
      ( map-hom-cocone-sequential-colimit f
        ( cocone-standard-sequential-colimit B))

  htpy-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-square-maps
      ( map-hom-sequential-diagram B f n)
      ( map-cocone-standard-sequential-colimit A n)
      ( map-cocone-standard-sequential-colimit B n)
      ( map-hom-standard-sequential-colimit)
  htpy-htpy-cocone-map-hom-standard-sequential-colimit =
    htpy-htpy-cocone-sequential-diagram A
      ( htpy-cocone-map-hom-standard-sequential-colimit)

  coherence-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    coherence-square-homotopies
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit n)
      ( map-hom-standard-sequential-colimit ·l
        ( coherence-triangle-cocone-standard-sequential-colimit A n))
      ( (
          pr2
          (map-hom-cocone-sequential-colimit f
          (cocone-standard-sequential-colimit B))
          n))
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n)
        ·r pr2 A n)
  coherence-htpy-cocone-map-hom-standard-sequential-colimit =
    coherence-htpy-htpy-cocone-sequential-diagram A
      ( htpy-cocone-map-hom-standard-sequential-colimit)

  prism-htpy-cocone-map-hom-standard-sequential-colimit :
    ( n : ℕ) →
    vertical-coherence-prism-maps
      ( map-sequential-diagram A n)
      ( map-cocone-standard-sequential-colimit A (succ-ℕ n))
      ( map-cocone-standard-sequential-colimit A n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-hom-standard-sequential-colimit)
      ( map-sequential-diagram B n)
      ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
      ( map-cocone-standard-sequential-colimit B n)
      ( coherence-triangle-cocone-standard-sequential-colimit A n)
      ( naturality-map-hom-sequential-diagram B f n)
      ( inv-htpy
        ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n)))
      ( inv-htpy (htpy-htpy-cocone-map-hom-standard-sequential-colimit n))
      ( coherence-triangle-cocone-standard-sequential-colimit B n)
  prism-htpy-cocone-map-hom-standard-sequential-colimit n =
    [v]
      ( map-sequential-diagram A n)
      ( map-cocone-standard-sequential-colimit A (succ-ℕ n))
      ( map-cocone-standard-sequential-colimit A n)
      ( map-hom-sequential-diagram B f n)
      ( map-hom-sequential-diagram B f (succ-ℕ n))
      ( map-hom-standard-sequential-colimit)
      ( map-sequential-diagram B n)
      ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
      ( map-cocone-standard-sequential-colimit B n)
      ( coherence-triangle-cocone-standard-sequential-colimit A n)
      ( naturality-map-hom-sequential-diagram B f n)
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit (succ-ℕ n))
      ( htpy-htpy-cocone-map-hom-standard-sequential-colimit n)
      ( coherence-triangle-cocone-standard-sequential-colimit B n)
      ( inv-htpy (coherence-htpy-cocone-map-hom-standard-sequential-colimit n))
```

### Homotopies between morphisms of sequential diagrams induce homotopies of maps of sequential colimits

```agda
module _
  { l1 l2 : Level} (A : sequential-diagram l1) {X : UU l2}
  { f g : standard-sequential-colimit A → X}
  ( H : htpy-standard-sequential-colimit A f g)
  where

  htpy-htpy-standard-sequential-colimit : f ~ g
  htpy-htpy-standard-sequential-colimit =
    map-dependent-universal-property-sequential-colimit A
      ( cocone-standard-sequential-colimit A)
      ( dup-standard-sequential-colimit A)
      ( pr1 H ,
        λ n a →
        map-compute-dependent-identification-eq-value-function f g
          ( coherence-triangle-cocone-standard-sequential-colimit A n a)
          ( pr1 H n a)
          ( (pr1 H (succ-ℕ n) ∘ pr2 A n) a)
          ( pr2 H n a))
```

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  { f g : hom-sequential-diagram A B} (H : htpy-hom-sequential-diagram B f g)
  where

  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram :
    map-hom-standard-sequential-colimit B f ~
    map-hom-standard-sequential-colimit B g
  htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram =
    htpy-eq
      ( ap
        ( map-hom-standard-sequential-colimit B)
        ( eq-htpy-sequential-diagram A B f g H))
```

### The identity morphism induces the identity map

```agda
module _
  { l1 : Level} (A : sequential-diagram l1)
  where

  preserves-id-map-hom-standard-sequential-colimit :
    map-hom-standard-sequential-colimit A
      ( id-hom-sequential-diagram A) ~
    id
  preserves-id-map-hom-standard-sequential-colimit =
    htpy-htpy-standard-sequential-colimit A
      ( ( htpy-htpy-cocone-map-hom-standard-sequential-colimit A
          ( id-hom-sequential-diagram A)) ,
        ( λ n →
          ( coherence-htpy-cocone-map-hom-standard-sequential-colimit A
            ( id-hom-sequential-diagram A) n) ∙h
          ( horizontal-concat-htpy² refl-htpy
            ( ( right-unit-htpy) ∙h
              ( inv-htpy
                ( left-unit-law-left-whisk-htpy
                  ( coherence-triangle-cocone-standard-sequential-colimit A
                    ( n))))))))
```

### Composition preservation

```agda
module _
  { l1 l2 l3 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  ( C : sequential-diagram l3)
  ( g : hom-sequential-diagram B C) (f : hom-sequential-diagram A B)
  where

  preserves-comp-map-hom-standard-sequential-colimit :
    map-hom-standard-sequential-colimit C
      ( comp-hom-sequential-diagram A B C g f) ~
    ( map-hom-standard-sequential-colimit C g ∘
      map-hom-standard-sequential-colimit B f)
  preserves-comp-map-hom-standard-sequential-colimit =
    htpy-htpy-standard-sequential-colimit A
      ( ( λ n →
          ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
            ( comp-hom-sequential-diagram A B C g f) n) ∙h
          ( pasting-vertical-coherence-square-maps
            ( map-cocone-standard-sequential-colimit A n)
            ( map-hom-sequential-diagram B f n)
            ( map-hom-standard-sequential-colimit B f)
            ( map-cocone-standard-sequential-colimit B n)
            ( map-hom-sequential-diagram C g n)
            ( map-hom-standard-sequential-colimit C g)
            ( map-cocone-standard-sequential-colimit C n)
            ( inv-htpy
              ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f n))
            ( inv-htpy
              ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g n)))) ,
        ( λ n →
          ( inv-htpy-assoc-htpy
            ( ( map-hom-standard-sequential-colimit C
                ( comp-hom-sequential-diagram A B C g f)) ·l
              ( coherence-triangle-cocone-standard-sequential-colimit A n))
            ( ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
                ( comp-hom-sequential-diagram A B C g f)
                ( succ-ℕ n)) ·r
              ( map-sequential-diagram A n))
            ( ( pasting-vertical-coherence-square-maps
                ( map-cocone-standard-sequential-colimit A (succ-ℕ n))
                ( map-hom-sequential-diagram B f (succ-ℕ n))
                ( map-hom-standard-sequential-colimit B f)
                ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
                ( map-hom-sequential-diagram C g (succ-ℕ n))
                ( map-hom-standard-sequential-colimit C g)
                ( map-cocone-standard-sequential-colimit C (succ-ℕ n))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f
                    ( succ-ℕ n)))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g
                    ( succ-ℕ n)))) ·r
              ( map-sequential-diagram A n))) ∙h
          ( ap-concat-htpy'
            ( ( pasting-vertical-coherence-square-maps
                ( map-cocone-standard-sequential-colimit A (succ-ℕ n))
                ( map-hom-sequential-diagram B f (succ-ℕ n))
                ( map-hom-standard-sequential-colimit B f)
                ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
                ( map-hom-sequential-diagram C g (succ-ℕ n))
                ( map-hom-standard-sequential-colimit C g)
                ( map-cocone-standard-sequential-colimit C (succ-ℕ n))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f
                    ( succ-ℕ n)))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g
                    ( succ-ℕ n)))) ·r
              ( map-sequential-diagram A n))
            ( coherence-htpy-cocone-map-hom-standard-sequential-colimit C
              ( comp-hom-sequential-diagram A B C g f)
              ( n)) ∙h
          ( assoc-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
              ( comp-hom-sequential-diagram A B C g f)
              ( n))
            ( coherence-triangle-cocone-sequential-diagram A
              ( map-hom-cocone-sequential-colimit
                ( comp-hom-sequential-diagram A B C g f)
                ( cocone-standard-sequential-colimit C))
              ( n))
            ( ( pasting-vertical-coherence-square-maps
                ( map-cocone-standard-sequential-colimit A (succ-ℕ n))
                ( map-hom-sequential-diagram B f (succ-ℕ n))
                ( map-hom-standard-sequential-colimit B f)
                ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
                ( map-hom-sequential-diagram C g (succ-ℕ n))
                ( map-hom-standard-sequential-colimit C g)
                ( map-cocone-standard-sequential-colimit C (succ-ℕ n))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f
                    ( succ-ℕ n)))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g
                    ( succ-ℕ n)))) ·r
              ( map-sequential-diagram A n))) ∙h
          ( ap-concat-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
              ( comp-hom-sequential-diagram A B C g f)
              ( n))
            ( ( assoc-htpy
                ( ( coherence-triangle-cocone-standard-sequential-colimit C
                    ( n)) ·r
                  ( ( map-hom-sequential-diagram C g n) ∘
                    ( map-hom-sequential-diagram B f n)))
                ( map-cocone-standard-sequential-colimit C (succ-ℕ n) ·l _)
                ( _)) ∙h
              ( pasting-vertical-coherence-prism-maps
                ( map-sequential-diagram A n)
                ( map-cocone-standard-sequential-colimit A (succ-ℕ n))
                ( map-cocone-standard-sequential-colimit A n)
                ( map-hom-sequential-diagram B f n)
                ( map-hom-sequential-diagram B f (succ-ℕ n))
                ( map-hom-standard-sequential-colimit B f)
                ( map-sequential-diagram B n)
                ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
                ( map-cocone-standard-sequential-colimit B n)
                ( map-hom-sequential-diagram C g n)
                ( map-hom-sequential-diagram C g (succ-ℕ n))
                ( map-hom-standard-sequential-colimit C g)
                ( map-sequential-diagram C n)
                ( map-cocone-standard-sequential-colimit C (succ-ℕ n))
                ( map-cocone-standard-sequential-colimit C n)
                ( coherence-triangle-cocone-standard-sequential-colimit A n)
                ( naturality-map-hom-sequential-diagram B f n)
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f
                    ( succ-ℕ n)))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f n))
                ( coherence-triangle-cocone-standard-sequential-colimit B n)
                ( naturality-map-hom-sequential-diagram C g n)
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g
                    ( succ-ℕ n)))
                ( inv-htpy
                  ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g n))
                ( coherence-triangle-cocone-standard-sequential-colimit C n)
                ( prism-htpy-cocone-map-hom-standard-sequential-colimit B f n)
                ( prism-htpy-cocone-map-hom-standard-sequential-colimit C g
                  ( n))))) ∙h
          ( inv-htpy-assoc-htpy
            ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C
              ( comp-hom-sequential-diagram A B C g f)
              ( n))
            ( pasting-vertical-coherence-square-maps
              ( map-cocone-standard-sequential-colimit A n)
              ( map-hom-sequential-diagram B f n)
              ( map-hom-standard-sequential-colimit B f)
              ( map-cocone-standard-sequential-colimit B n)
              ( map-hom-sequential-diagram C g n)
              ( map-hom-standard-sequential-colimit C g)
              ( map-cocone-standard-sequential-colimit C n)
              ( inv-htpy
                ( htpy-htpy-cocone-map-hom-standard-sequential-colimit B f
                  ( n)))
              ( inv-htpy
                ( htpy-htpy-cocone-map-hom-standard-sequential-colimit C g
                  ( n))))
            ( ( ( map-hom-standard-sequential-colimit C g) ∘
                  ( map-hom-standard-sequential-colimit B f)) ·l
                ( coherence-triangle-cocone-standard-sequential-colimit A
                  ( n)))))))
```

### An equivalence of sequential diagrams induces an equivalence of cocones

```agda
module _
  { l1 l2 : Level} {A : sequential-diagram l1} {B : sequential-diagram l2}
  ( e : equiv-sequential-diagram A B)
  where

  map-equiv-standard-sequential-colimit :
    standard-sequential-colimit A → standard-sequential-colimit B
  map-equiv-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B
      ( hom-equiv-sequential-diagram B e)

  inv-map-equiv-standard-sequential-colimit :
    standard-sequential-colimit B → standard-sequential-colimit A
  inv-map-equiv-standard-sequential-colimit =
    map-hom-standard-sequential-colimit A
      ( hom-inv-equiv-sequential-diagram B e)

  abstract
    is-section-inv-map-equiv-standard-sequential-colimit :
      ( map-equiv-standard-sequential-colimit) ∘
      ( inv-map-equiv-standard-sequential-colimit) ~
      id
    is-section-inv-map-equiv-standard-sequential-colimit =
      ( inv-htpy
        ( preserves-comp-map-hom-standard-sequential-colimit B A B
          ( hom-equiv-sequential-diagram B e)
          ( hom-inv-equiv-sequential-diagram B e))) ∙h
      ( htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram
        ( ( λ n →
            is-section-map-inv-equiv (equiv-equiv-sequential-diagram B e n)) ,
          ( λ n →
            inv-htpy
              ( right-inverse-law-pasting-vertical-coherence-square-maps
                ( map-sequential-diagram A n)
                ( equiv-equiv-sequential-diagram B e n)
                ( equiv-equiv-sequential-diagram B e (succ-ℕ n))
                ( map-sequential-diagram B n)
                ( naturality-equiv-sequential-diagram B e n))))) ∙h
      ( preserves-id-map-hom-standard-sequential-colimit B)

    is-retraction-inv-map-equiv-standard-sequential-colimit :
      ( inv-map-equiv-standard-sequential-colimit) ∘
      ( map-equiv-standard-sequential-colimit) ~
      id
    is-retraction-inv-map-equiv-standard-sequential-colimit =
      ( inv-htpy
        ( preserves-comp-map-hom-standard-sequential-colimit A B A
          ( hom-inv-equiv-sequential-diagram B e)
          ( hom-equiv-sequential-diagram B e))) ∙h
      ( htpy-map-hom-standard-sequential-colimit-htpy-hom-sequential-diagram
        ( ( λ n →
            is-retraction-map-inv-equiv
              ( equiv-equiv-sequential-diagram B e n)) ,
          ( λ n →
            inv-htpy
              ( left-inverse-law-pasting-vertical-coherence-square-maps
                ( map-sequential-diagram A n)
                ( equiv-equiv-sequential-diagram B e n)
                ( equiv-equiv-sequential-diagram B e (succ-ℕ n))
                ( map-sequential-diagram B n)
                ( naturality-equiv-sequential-diagram B e n))))) ∙h
      ( preserves-id-map-hom-standard-sequential-colimit A)

  -- equiv-cocone-equiv-sequential-diagram :
  --   { l3 : Level} {X : UU l3} →
  --   cocone-sequential-diagram B X ≃ cocone-sequential-diagram A X
  -- equiv-cocone-equiv-sequential-diagram {X = X} =
  --   equiv-precomp-equiv-hom-sequential-diagram A B
  --     ( constant-sequential-diagram X)
  --     ( e)

  -- triangle-equiv-cocone-equiv-sequential-diagram :
  --   { l3 : Level} {X : UU l3} →
  --   coherence-triangle-maps
  --     ( cocone-map-sequential-diagram A
  --       ( map-hom-cocone-sequential-colimit
  --         ( hom-equiv-sequential-diagram B e)
  --         ( cocone-standard-sequential-colimit B))
  --       { Y = X})
  --     ( map-equiv equiv-cocone-equiv-sequential-diagram)
  --     ( cocone-map-sequential-diagram B (cocone-standard-sequential-colimit B))
  -- triangle-equiv-cocone-equiv-sequential-diagram h =
  --   eq-htpy-cocone-sequential-diagram A _ _
  --     ( ( λ n → refl-htpy) ,
  --       ( λ n →
  --         ( right-unit-htpy) ∙h
  --         ( λ a →
  --           ( distributive-left-whisk-concat-htpy h
  --             ( ( coherence-triangle-cocone-sequential-diagram B
  --                 ( cocone-standard-sequential-colimit B)
  --                 ( n)) ·r
  --               ( map-equiv-sequential-diagram B e n))
  --             ( ( map-cocone-sequential-diagram B
  --                 ( cocone-standard-sequential-colimit B)
  --                 ( succ-ℕ n) ·l
  --               ( naturality-map-hom-sequential-diagram B
  --                 ( hom-equiv-sequential-diagram B e) n)))
  --             ( a)) ∙
  --           ( ap
  --             ( ap h
  --               ( coherence-triangle-cocone-sequential-diagram B
  --                 ( cocone-standard-sequential-colimit B)
  --                 ( n)
  --                 ( map-equiv-sequential-diagram B e n a)) ∙_)
  --             ( associative-left-whisk-comp h
  --               ( map-cocone-standard-sequential-colimit B (succ-ℕ n))
  --               ( naturality-equiv-sequential-diagram B e n)
  --               ( a))))))

  -- map-up-cocone-equiv-sequential-diagram :
  --   ( {l : Level} →
  --     universal-property-sequential-colimit l A
  --       ( map-hom-cocone-sequential-colimit
  --         ( hom-equiv-sequential-diagram B e)
  --         ( cocone-standard-sequential-colimit B)))
  -- map-up-cocone-equiv-sequential-diagram Y =
  --   is-equiv-left-map-triangle
  --     ( cocone-map-sequential-diagram A
  --       ( map-hom-cocone-sequential-colimit
  --         ( hom-equiv-sequential-diagram B e)
  --         ( cocone-standard-sequential-colimit B)))
  --     ( map-equiv equiv-cocone-equiv-sequential-diagram)
  --     ( cocone-map-sequential-diagram B (cocone-standard-sequential-colimit B))
  --     ( triangle-equiv-cocone-equiv-sequential-diagram)
  --     ( up-standard-sequential-colimit B Y)
  --     ( is-equiv-map-equiv equiv-cocone-equiv-sequential-diagram)

  -- is-equiv-map-hom-standard-sequential-colimit :
  --   is-equiv map-equiv-standard-sequential-colimit
  -- is-equiv-map-hom-standard-sequential-colimit =
  --   is-equiv-universal-property-sequential-colimit-universal-property-sequential-colimit
  --     ( A)
  --     ( cocone-standard-sequential-colimit A)
  --     ( map-hom-cocone-sequential-colimit
  --       ( hom-equiv-sequential-diagram B e)
  --       ( cocone-standard-sequential-colimit B))
  --     ( map-hom-standard-sequential-colimit B
  --       ( hom-equiv-sequential-diagram B e))
  --     ( htpy-cocone-map-hom-standard-sequential-colimit B
  --       ( hom-equiv-sequential-diagram B e))
  --     ( up-standard-sequential-colimit A)
  --     ( map-up-cocone-equiv-sequential-diagram)

  is-equiv-map-hom-standard-sequential-colimit' :
    is-equiv map-equiv-standard-sequential-colimit
  is-equiv-map-hom-standard-sequential-colimit' =
    is-equiv-is-invertible
      ( inv-map-equiv-standard-sequential-colimit)
      ( is-section-inv-map-equiv-standard-sequential-colimit)
      ( is-retraction-inv-map-equiv-standard-sequential-colimit)

  equiv-equiv-standard-sequential-colimit :
    standard-sequential-colimit A ≃ standard-sequential-colimit B
  pr1 equiv-equiv-standard-sequential-colimit =
    map-hom-standard-sequential-colimit B
      ( hom-equiv-sequential-diagram B e)
  pr2 equiv-equiv-standard-sequential-colimit =
    is-equiv-map-hom-standard-sequential-colimit'
```
