# Functoriality stuff

```agda
{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}

module synthetic-homotopy-theory.functoriality-stuff where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
-- open import foundation.binary-homotopies
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
-- open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
-- open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.implicit-function-types
open import foundation.postcomposition-functions
open import foundation.precomposition-dependent-functions
open import foundation.transport-along-identifications
-- open import foundation.transposition-identifications-along-equivalences
open import foundation.universal-property-equivalences
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
-- open import foundation.whiskering-homotopies-concatenation

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-sequential-diagrams
open import synthetic-homotopy-theory.dependent-universal-property-sequential-colimits
open import synthetic-homotopy-theory.descent-data-sequential-colimits
open import synthetic-homotopy-theory.functoriality-sequential-colimits
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
open import synthetic-homotopy-theory.stuff-over
open import synthetic-homotopy-theory.universal-property-sequential-colimits
```

</details>

## Theorem

New idea: instead of bruteforcing this direction, show that a square induces
coherent cubes, and show that it's an equivalence because it fits in a diagram.

## Commuting cubes induce commuting squares in the colimit

```agda
open import foundation.commuting-cubes-of-maps
module _
  {l1 l2 l3 l4 l5 l6 l7 l8 : Level}
  {A : sequential-diagram l1} {X : UU l2} {a : cocone-sequential-diagram A X}
  (up-a : universal-property-sequential-colimit a)
  {B : sequential-diagram l3} {Y : UU l4} {b : cocone-sequential-diagram B Y}
  (up-b : universal-property-sequential-colimit b)
  {P : sequential-diagram l5} {V : UU l6} {p : cocone-sequential-diagram P V}
  (up-p : universal-property-sequential-colimit p)
  {Q : sequential-diagram l7} {W : UU l8} {q : cocone-sequential-diagram Q W}
  (up-q : universal-property-sequential-colimit q)
  (f' : hom-sequential-diagram P Q)
  (f : hom-sequential-diagram A B)
  (g : hom-sequential-diagram P A)
  (h : hom-sequential-diagram Q B)
  where

  square-cube-sequential-colimit :
    (faces :
      (n : ℕ) →
      coherence-square-maps
        ( map-hom-sequential-diagram Q f' n)
        ( map-hom-sequential-diagram A g n)
        ( map-hom-sequential-diagram B h n)
        ( map-hom-sequential-diagram B f n)) →
    (cubes :
      (n : ℕ) →
      coherence-cube-maps
        ( map-hom-sequential-diagram B f n)
        ( map-sequential-diagram A n)
        ( map-sequential-diagram B n)
        ( map-hom-sequential-diagram B f (succ-ℕ n))
        ( map-hom-sequential-diagram Q f' n)
        ( map-sequential-diagram P n)
        ( map-sequential-diagram Q n)
        ( map-hom-sequential-diagram Q f' (succ-ℕ n))
        ( map-hom-sequential-diagram A g n)
        ( map-hom-sequential-diagram B h n)
        ( map-hom-sequential-diagram A g (succ-ℕ n))
        ( map-hom-sequential-diagram B h (succ-ℕ n))
        ( naturality-map-hom-sequential-diagram Q f' n)
        ( faces n)
        ( naturality-map-hom-sequential-diagram A g n)
        ( naturality-map-hom-sequential-diagram B h n)
        ( faces (succ-ℕ n))
        ( naturality-map-hom-sequential-diagram B f n)) →
    coherence-square-maps
      ( map-sequential-colimit-hom-sequential-diagram up-p q f')
      ( map-sequential-colimit-hom-sequential-diagram up-p a g)
      ( map-sequential-colimit-hom-sequential-diagram up-q b h)
      ( map-sequential-colimit-hom-sequential-diagram up-a b f)
  square-cube-sequential-colimit faces cubes =
    inv-htpy
      ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-p up-a b
        f g) ∙h
    induced-htpy ∙h
    preserves-comp-map-sequential-colimit-hom-sequential-diagram up-p up-q b h f'
    where
    comp1 comp2 : hom-sequential-diagram P B
    comp1 = comp-hom-sequential-diagram P A B f g
    comp2 = comp-hom-sequential-diagram P Q B h f'
    induced-hom-htpy : htpy-hom-sequential-diagram B comp1 comp2
    pr1 induced-hom-htpy = faces
    pr2 induced-hom-htpy n =
      assoc-htpy _ _ _ ∙h
      inv-htpy (cubes n) ∙h
      assoc-htpy _ _ _
    induced-htpy :
      map-sequential-colimit-hom-sequential-diagram up-p b comp1 ~
      map-sequential-colimit-hom-sequential-diagram up-p b comp2
    induced-htpy =
      htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-p b
        ( induced-hom-htpy)
```

## Concatenation of homotopies of morphisms of sequential diagrams

```agda
open import foundation.whiskering-homotopies-concatenation
module _
  {l1 l2 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  (f g h : hom-sequential-diagram A B)
  where

  module _
    (H : htpy-hom-sequential-diagram B f g)
    (K : htpy-hom-sequential-diagram B g h)
    where

    concat-htpy-hom-sequential-diagram : htpy-hom-sequential-diagram B f h
    pr1 concat-htpy-hom-sequential-diagram n =
      htpy-htpy-hom-sequential-diagram _ H n ∙h
      htpy-htpy-hom-sequential-diagram _ K n
    pr2 concat-htpy-hom-sequential-diagram n =
      inv-htpy-assoc-htpy _ _ _ ∙h
      right-whisker-concat-htpy
        ( coherence-htpy-htpy-hom-sequential-diagram B H n)
        ( htpy-htpy-hom-sequential-diagram _ K (succ-ℕ n) ·r map-sequential-diagram A n) ∙h
      assoc-htpy _ _ _ ∙h
      left-whisker-concat-htpy
        ( map-sequential-diagram B n ·l htpy-htpy-hom-sequential-diagram _ H n)
        ( coherence-htpy-htpy-hom-sequential-diagram B K n) ∙h
      inv-htpy-assoc-htpy _ _ _ ∙h
      right-whisker-concat-htpy
        ( inv-htpy
          ( distributive-left-whisker-comp-concat
            ( map-sequential-diagram B n)
            ( htpy-htpy-hom-sequential-diagram _ H n)
            ( htpy-htpy-hom-sequential-diagram _ K n)))
        ( naturality-map-hom-sequential-diagram B h n)

  htpy-eq-concat-hom-sequential-diagram :
    (p : f ＝ g) (q : g ＝ h) →
    htpy-eq-sequential-diagram A B f h (p ∙ q) ＝
    concat-htpy-hom-sequential-diagram
      ( htpy-eq-sequential-diagram A B f g p)
      ( htpy-eq-sequential-diagram A B g h q)
  htpy-eq-concat-hom-sequential-diagram refl refl =
    eq-pair-eq-fiber
      ( inv
        ( eq-binary-htpy _ _
          λ n a →
          right-unit ∙ right-unit ∙
          ap
            ( (inv (assoc _ refl refl) ∙ ap (_∙ refl) right-unit) ∙ refl ∙_)
            ( ap-id right-unit) ∙
          ap
            ( _∙ right-unit)
            ( right-unit ∙
              ap
                ( λ p → inv p ∙ ap (_∙ refl) right-unit)
                ( middle-unit-law-assoc
                    ( naturality-map-hom-sequential-diagram B f n a)
                    ( refl)) ∙
              left-inv (ap (_∙ refl) right-unit))))
    where
      open import foundation.binary-homotopies
      open import foundation.path-algebra

  eq-htpy-concat-hom-sequential-diagram :
    (H : htpy-hom-sequential-diagram B f g)
    (K : htpy-hom-sequential-diagram B g h) →
    eq-htpy-sequential-diagram A B f h
      ( concat-htpy-hom-sequential-diagram H K) ＝
    eq-htpy-sequential-diagram A B f g H ∙
    eq-htpy-sequential-diagram A B g h K
  eq-htpy-concat-hom-sequential-diagram H K =
    ap
      ( eq-htpy-sequential-diagram A B f h)
      ( inv
        ( htpy-eq-concat-hom-sequential-diagram
          ( eq-htpy-sequential-diagram A B f g H)
          ( eq-htpy-sequential-diagram A B g h K) ∙
        ap-binary concat-htpy-hom-sequential-diagram
          ( is-section-map-inv-equiv
            ( extensionality-hom-sequential-diagram A B f g)
            ( H))
          ( is-section-map-inv-equiv
            ( extensionality-hom-sequential-diagram A B g h)
            ( K)))) ∙
    is-retraction-map-inv-equiv
      ( extensionality-hom-sequential-diagram A B f h)
      ( eq-htpy-sequential-diagram A B f g H ∙
        eq-htpy-sequential-diagram A B g h K)
    where open import foundation.action-on-identifications-binary-functions
```

## Whiskering of homotopies of morphisms of sequential diagrams

### Right whiskering

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3}
  where

  htpy-eq-right-whisker :
    {f g : B → C} (p : f ＝ g) (h : A → B) →
    htpy-eq (ap (_∘ h) p) ＝ htpy-eq p ·r h
  htpy-eq-right-whisker refl h = refl

  eq-htpy-right-whisker :
    {f g : B → C} (H : f ~ g) (h : A → B) →
    eq-htpy (H ·r h) ＝ ap (_∘ h) (eq-htpy H)
  eq-htpy-right-whisker H h =
    ap eq-htpy
      ( inv
        ( htpy-eq-right-whisker (eq-htpy H) h ∙
          ap (_·r h) (is-section-eq-htpy H))) ∙
    is-retraction-eq-htpy (ap (_∘ h) (eq-htpy H))

  htpy-eq-left-whisker :
    {f g : A → B} (h : B → C) (p : f ＝ g) →
    htpy-eq (ap (h ∘_) p) ＝ h ·l htpy-eq p
  htpy-eq-left-whisker h refl = refl

  -- alternatively, using homotopy induction
  eq-htpy-left-whisker :
    {f g : A → B} (h : B → C) (H : f ~ g) →
    eq-htpy (h ·l H) ＝ ap (h ∘_) (eq-htpy H)
  eq-htpy-left-whisker {f} h =
    ind-htpy f
      ( λ g H →
        eq-htpy (h ·l H) ＝ ap (h ∘_) (eq-htpy H))
      ( eq-htpy-refl-htpy (h ∘ f) ∙
        inv (ap (ap (h ∘_)) (eq-htpy-refl-htpy f)))
    where open import foundation.homotopy-induction
```

```agda
module _
  {l1 l2 l3 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : sequential-diagram l3}
  {f g : hom-sequential-diagram A B}
  where
  open import foundation.whiskering-identifications-concatenation

  module _
    (H : htpy-hom-sequential-diagram B f g)
    (h : hom-sequential-diagram X A)
    where

    right-whisker-concat-htpy-hom-sequential-diagram :
      htpy-hom-sequential-diagram B
        ( comp-hom-sequential-diagram X A B f h)
        ( comp-hom-sequential-diagram X A B g h)
    pr1 right-whisker-concat-htpy-hom-sequential-diagram n =
      htpy-htpy-hom-sequential-diagram _ H n ·r map-hom-sequential-diagram A h n
    pr2 right-whisker-concat-htpy-hom-sequential-diagram n x =
      assoc _ _ _ ∙
      left-whisker-concat
        ( naturality-map-hom-sequential-diagram B f n (map-hom-sequential-diagram A h n x))
        ( inv-nat-htpy
          ( htpy-htpy-hom-sequential-diagram B H (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram A h n x)) ∙
      inv (assoc _ _ _) ∙
      right-whisker-concat
        ( coherence-htpy-htpy-hom-sequential-diagram B H n (map-hom-sequential-diagram A h n x))
        ( ap
          ( map-hom-sequential-diagram B g (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram A h n x)) ∙
      assoc _ _ _

  htpy-eq-right-whisker-htpy-hom-sequential-diagram :
    (p : f ＝ g) (h : hom-sequential-diagram X A) →
    htpy-eq-sequential-diagram X B
      ( comp-hom-sequential-diagram X A B f h)
      ( comp-hom-sequential-diagram X A B g h)
      ( ap (λ f → comp-hom-sequential-diagram X A B f h) p) ＝
    right-whisker-concat-htpy-hom-sequential-diagram
      ( htpy-eq-sequential-diagram A B f g p)
      ( h)
  htpy-eq-right-whisker-htpy-hom-sequential-diagram refl h =
    eq-pair-eq-fiber
      ( eq-binary-htpy _ _
        λ n x →
        inv
          ( right-unit ∙
            ap-binary
              ( λ p q →
                p ∙
                left-whisker-concat _ q ∙
                inv (assoc _ refl _) ∙
                right-whisker-concat _ _)
              ( right-unit-law-assoc _ _)
              ( inv-nat-refl-htpy _ _) ∙
            ap
              ( λ p →
                right-unit ∙
                left-whisker-concat _ (inv right-unit) ∙
                left-whisker-concat _ right-unit ∙
                inv p ∙
                right-whisker-concat right-unit _)
              ( middle-unit-law-assoc _ _) ∙
            is-section-inv-concat'
              ( right-whisker-concat right-unit _)
              ( right-unit ∙
                left-whisker-concat _ (inv right-unit) ∙
                left-whisker-concat _ right-unit) ∙
            ap
              ( λ p → right-unit ∙ p ∙ left-whisker-concat _ right-unit)
              ( ap-inv (naturality-map-hom-sequential-diagram B f n _ ∙_) right-unit) ∙
            is-section-inv-concat'
              ( ap (naturality-map-hom-sequential-diagram B f n _ ∙_) right-unit)
              ( right-unit)))
    where
      open import foundation.binary-homotopies
      open import foundation.path-algebra
      open import foundation.action-on-identifications-binary-functions

  eq-htpy-right-whisker-htpy-hom-sequential-diagram :
    (H : htpy-hom-sequential-diagram B f g) (h : hom-sequential-diagram X A) →
    eq-htpy-sequential-diagram X B
      ( comp-hom-sequential-diagram X A B f h)
      ( comp-hom-sequential-diagram X A B g h)
      ( right-whisker-concat-htpy-hom-sequential-diagram H h) ＝
    ap
      ( λ f → comp-hom-sequential-diagram X A B f h)
      ( eq-htpy-sequential-diagram A B f g H)
  eq-htpy-right-whisker-htpy-hom-sequential-diagram H h =
    ap
      ( eq-htpy-sequential-diagram X B _ _)
      ( inv
        ( htpy-eq-right-whisker-htpy-hom-sequential-diagram
            ( eq-htpy-sequential-diagram A B f g H)
            ( h) ∙
          ap
            ( λ H → right-whisker-concat-htpy-hom-sequential-diagram H h)
            ( is-section-map-inv-equiv
              ( extensionality-hom-sequential-diagram A B f g)
              ( H)))) ∙
    is-retraction-map-inv-equiv
      ( extensionality-hom-sequential-diagram X B
        ( comp-hom-sequential-diagram X A B f h)
        ( comp-hom-sequential-diagram X A B g h))
      ( ap
        ( λ f → comp-hom-sequential-diagram X A B f h)
        ( eq-htpy-sequential-diagram A B f g H))
```

### Left whiskering

```agda
module _
  {l1 l2 l3 : Level}
  {A : sequential-diagram l1} {B : sequential-diagram l2}
  {X : sequential-diagram l3}
  (h : hom-sequential-diagram B X)
  {f g : hom-sequential-diagram A B}
  (H : htpy-hom-sequential-diagram B f g)
  where
  open import foundation.whiskering-identifications-concatenation

  left-whisker-concat-htpy-hom-sequential-diagram :
    htpy-hom-sequential-diagram X
      ( comp-hom-sequential-diagram A B X h f)
      ( comp-hom-sequential-diagram A B X h g)
  pr1 left-whisker-concat-htpy-hom-sequential-diagram n =
    map-hom-sequential-diagram X h n ·l htpy-htpy-hom-sequential-diagram _ H n
  pr2 left-whisker-concat-htpy-hom-sequential-diagram n a =
    assoc _ _ _ ∙
    left-whisker-concat
      ( naturality-map-hom-sequential-diagram X h n (map-hom-sequential-diagram B f n a))
      ( inv (ap-concat (map-hom-sequential-diagram X h (succ-ℕ n)) _ _) ∙
        ap
          ( ap (map-hom-sequential-diagram X h (succ-ℕ n)))
          ( coherence-htpy-htpy-hom-sequential-diagram B H n a) ∙
        ap-concat (map-hom-sequential-diagram X h (succ-ℕ n)) _ _) ∙
    inv (assoc _ _ _) ∙
    right-whisker-concat
      ( left-whisker-concat
          ( naturality-map-hom-sequential-diagram X h n
            ( map-hom-sequential-diagram B f n a))
          ( inv
            ( ap-comp
              ( map-hom-sequential-diagram X h (succ-ℕ n))
              ( map-sequential-diagram B n)
              ( htpy-htpy-hom-sequential-diagram B H n a))) ∙
        nat-htpy
          ( naturality-map-hom-sequential-diagram X h n)
          ( htpy-htpy-hom-sequential-diagram B H n a) ∙
        right-whisker-concat
          ( ap-comp
            ( map-sequential-diagram X n)
            ( map-hom-sequential-diagram X h n)
            ( htpy-htpy-hom-sequential-diagram B H n a))
          ( naturality-map-hom-sequential-diagram X h n
            ( map-hom-sequential-diagram B g n a)))
      ( ap
        ( map-hom-sequential-diagram X h (succ-ℕ n))
        ( naturality-map-hom-sequential-diagram B g n a)) ∙
    assoc _ _ _
```

## Action on homotopies of morphisms of sequential diagrams preserves whiskering

```agda
-- module _
--   {l1 l2 l3 l4 l5 l6 : Level}
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {X : UU l2} {a : cocone-sequential-diagram A X}
  (up-a : universal-property-sequential-colimit a)
  {B : sequential-diagram l3} {Y : UU l4} {b : cocone-sequential-diagram B Y}
  (up-b : universal-property-sequential-colimit b)
  {C : sequential-diagram l5} {Z : UU l6} (c : cocone-sequential-diagram C Z)
  {f g : hom-sequential-diagram B C}
  (H : htpy-hom-sequential-diagram C f g)
  (h : hom-sequential-diagram A B)
  where

  preserves-right-whisker-htpy-hom-sequential-diagram :
    ( ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-a c
        ( right-whisker-concat-htpy-hom-sequential-diagram H h)) ∙h
      ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-a up-b c g h)) ~
    ( ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-a up-b c f h) ∙h
      ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-b c H ·r
        map-sequential-colimit-hom-sequential-diagram up-a b h))
  preserves-right-whisker-htpy-hom-sequential-diagram =
    right-whisker-concat-htpy
      ( htpy-eq
        ( ap
          ( λ p →
            htpy-eq
              ( ap (map-sequential-colimit-hom-sequential-diagram up-a c) p))
          ( eq-htpy-right-whisker-htpy-hom-sequential-diagram H h)))
      ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-a up-b c g h) ∙h
    {!!}
```

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  {A : sequential-diagram l1} {X : UU l2} {a : cocone-sequential-diagram A X}
  (up-a : universal-property-sequential-colimit a)
  {B : sequential-diagram l3} {Y : UU l4} {b : cocone-sequential-diagram B Y}
  (up-b : universal-property-sequential-colimit b)
  {C : sequential-diagram l5} {Z : UU l6} (c : cocone-sequential-diagram C Z)
  (h : hom-sequential-diagram B C)
  {f g : hom-sequential-diagram A B}
  (H : htpy-hom-sequential-diagram B f g)
  where

  preserves-left-whisker-htpy-hom-sequential-diagram :
    ( ( htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-a c
        ( left-whisker-concat-htpy-hom-sequential-diagram h H)) ∙h
      ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-a up-b c h g)) ~
    ( ( preserves-comp-map-sequential-colimit-hom-sequential-diagram up-a up-b c h f) ∙h
      ( map-sequential-colimit-hom-sequential-diagram up-b c h ·l
        htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-a b H))
  preserves-left-whisker-htpy-hom-sequential-diagram = {!!}
```

## Action on homotopies of morphisms of sequential diagrams preserves concatenation

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} {a : cocone-sequential-diagram A X}
  (up-a : universal-property-sequential-colimit a)
  {B : sequential-diagram l3} {Y : UU l4} (b : cocone-sequential-diagram B Y)
  {f g h : hom-sequential-diagram A B}
  (H : htpy-hom-sequential-diagram B f g)
  (K : htpy-hom-sequential-diagram B g h)
  where

  preserves-concat-htpy-hom-sequential-diagram :
    htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-a b
      ( concat-htpy-hom-sequential-diagram f g h H K) ~
    htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-a b H ∙h
    htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-a b K
  preserves-concat-htpy-hom-sequential-diagram =
    htpy-eq
      ( ( ap
          ( λ p →
            htpy-eq
              ( ap
                ( map-sequential-colimit-hom-sequential-diagram up-a b)
                ( p)))
          ( eq-htpy-concat-hom-sequential-diagram f g h H K)) ∙
        ( ap htpy-eq
          ( ap-concat
            ( map-sequential-colimit-hom-sequential-diagram up-a b)
            ( eq-htpy-sequential-diagram A B f g H)
            ( eq-htpy-sequential-diagram A B g h K))) ∙
        ( htpy-eq-concat
          ( ap
            ( map-sequential-colimit-hom-sequential-diagram up-a b)
            ( eq-htpy-sequential-diagram A B f g H))
          ( ap
            ( map-sequential-colimit-hom-sequential-diagram up-a b)
            ( eq-htpy-sequential-diagram A B g h K))))
```

-- ```agda
-- nat-lemma :
--   {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2}
--   {P : A → UU l3} {Q : B → UU l4}
--   (f : A → B) (h : (a : A) → P a → Q (f a))
--   {x y : A} {p : x ＝ y}
--   {q : f x ＝ f y} (α : ap f p ＝ q) →
--   coherence-square-maps
--     ( tr P p)
--     ( h x)
--     ( h y)
--     ( tr Q q)
-- nat-lemma f h {p = p} refl x =
--   substitution-law-tr _ f p ∙ inv (preserves-tr h p x)
-- ```

-- ##

-- ```agda
-- open import synthetic-homotopy-theory.families-descent-data-sequential-colimits
-- open import synthetic-homotopy-theory.total-cocones-families-sequential-diagrams
-- open import synthetic-homotopy-theory.total-sequential-diagrams

-- open import foundation.action-on-identifications-functions
-- open import foundation.commuting-squares-of-identifications
-- open import foundation.functoriality-dependent-pair-types
-- open import foundation.equality-dependent-pair-types
-- open import foundation.identity-types
-- open import synthetic-homotopy-theory.sequential-colimits
-- open import synthetic-homotopy-theory.functoriality-sequential-colimits
-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : sequential-diagram l1}
--   {X : UU l2} {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   (P : family-with-descent-data-sequential-colimit c l3)
--   {Y : UU l4}
--   {c' :
--     cocone-sequential-diagram
--       ( total-sequential-diagram-family-with-descent-data-sequential-colimit P)
--       ( Y)}
--   (up-c' : universal-property-sequential-colimit c')
--   where

--   mediating-cocone :
--     cocone-sequential-diagram
--       ( total-sequential-diagram-family-with-descent-data-sequential-colimit P)
--       ( Σ X (family-cocone-family-with-descent-data-sequential-colimit P))
--   pr1 mediating-cocone n =
--     map-Σ
--       ( family-cocone-family-with-descent-data-sequential-colimit P)
--       ( map-cocone-sequential-diagram c n)
--       ( λ a → map-equiv-descent-data-family-with-descent-data-sequential-colimit P n a)
--   pr2 mediating-cocone n (a , p) =
--     eq-pair-Σ
--       ( coherence-cocone-sequential-diagram c n a)
--       ( inv
--         ( coherence-square-equiv-descent-data-family-with-descent-data-sequential-colimit P n a p))

--   totι' : Y → Σ X (family-cocone-family-with-descent-data-sequential-colimit P)
--   totι' =
--     map-universal-property-sequential-colimit up-c' mediating-cocone
--   triangle-pr1∞-pr1 :
--     pr1-sequential-colimit-total-sequential-diagram
--       ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit P)
--       ( up-c')
--       ( c) ~
--     pr1 ∘ totι'
--   triangle-pr1∞-pr1 =
--     htpy-htpy-out-of-sequential-colimit up-c'
--       ( concat-htpy-cocone-sequential-diagram
--         ( htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c' c
--           ( pr1-total-sequential-diagram
--             ( dependent-sequential-diagram-family-with-descent-data-sequential-colimit P)))
--         ( ( λ n →
--             inv-htpy (pr1 ·l (pr1 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) n))) ,
--           ( λ n x →
--             ap (_∙ inv (ap pr1 (pr1 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) (succ-ℕ n) _))) right-unit ∙
--             horizontal-inv-coherence-square-identifications _
--               ( ap (pr1 ∘ totι') (coherence-cocone-sequential-diagram c' n x))
--               ( coherence-cocone-sequential-diagram c n (pr1 x))
--               _
--               ( ( ap
--                   ( _∙ ap pr1
--                     ( pr1 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) (succ-ℕ n) _))
--                   ( ap-comp pr1
--                     ( totι')
--                     ( coherence-cocone-sequential-diagram c' n x))) ∙
--                 ( inv
--                   ( ap-concat pr1
--                     ( ap
--                       ( totι')
--                       ( coherence-cocone-sequential-diagram c' n x)) _)) ∙
--                 ( ap (ap pr1) (pr2 (htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone) n x)) ∙
--                 ( ap-concat pr1
--                   ( pr1
--                     ( htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone)
--                     n x)
--                   ( coherence-cocone-sequential-diagram mediating-cocone n x)) ∙
--                 ( ap
--                   ( ap pr1
--                     ( pr1
--                       ( htpy-cocone-universal-property-sequential-colimit up-c' mediating-cocone)
--                       n x) ∙_)
--                   ( ap-pr1-eq-pair-Σ
--                     ( coherence-cocone-sequential-diagram c n (pr1 x))
--                     ( _)))))))
-- ```

-- ```agda
-- module _
--   {l1 l2 : Level}
--   {A : sequential-diagram l1}
--   (P : descent-data-sequential-colimit A l2)
--   where

--   section-descent-data-sequential-colimit : UU (l1 ⊔ l2)
--   section-descent-data-sequential-colimit =
--     Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
--         family-descent-data-sequential-colimit P n a)
--       ( λ s →
--         (n : ℕ) (a : family-sequential-diagram A n) →
--         map-family-descent-data-sequential-colimit P n a (s n a) ＝
--         s (succ-ℕ n) (map-sequential-diagram A n a))

-- module _
--   {l1 l2 l3 : Level}
--   {A : sequential-diagram l1}
--   {X : UU l2} {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   (P : X → UU l3)
--   where

--   sect-family-sect-dd-sequential-colimit :
--     section-descent-data-sequential-colimit
--       ( descent-data-family-cocone-sequential-diagram c P) →
--     ((x : X) → P x)
--   sect-family-sect-dd-sequential-colimit s =
--     map-dependent-universal-property-sequential-colimit
--       ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
--       ( s)
-- ```

-- ```agda
-- module _
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : sequential-diagram l1} {X : UU l2}
--   {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   {B : sequential-diagram l3} {Y : UU l4}
--   {c' : cocone-sequential-diagram B Y}
--   (up-c' : universal-property-sequential-colimit c')
--   (P : X → UU l5) (Q : Y → UU l6)
--   (f : hom-sequential-diagram A B)
--   (f' :
--     (x : X) → P x →
--     Q (map-sequential-colimit-hom-sequential-diagram up-c c' f x))
--   where

--   open import synthetic-homotopy-theory.flattening-lemma-sequential-colimits

--   ΣAP : sequential-diagram (l1 ⊔ l5)
--   ΣAP =
--     total-sequential-diagram (dependent-sequential-diagram-family-cocone c P)

--   ΣBQ : sequential-diagram (l3 ⊔ l6)
--   ΣBQ =
--     total-sequential-diagram (dependent-sequential-diagram-family-cocone c' Q)

--   private
--     finf : X → Y
--     finf = (map-sequential-colimit-hom-sequential-diagram up-c c' f)

--   totff' : hom-sequential-diagram ΣAP ΣBQ
--   pr1 totff' n =
--     map-Σ _
--       ( map-hom-sequential-diagram B f n)
--       ( λ a →
--         tr Q
--           ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--             up-c c' f n a) ∘
--         f' (map-cocone-sequential-diagram c n a))
--   pr2 totff' n (a , p) =
--     eq-pair-Σ
--       ( naturality-map-hom-sequential-diagram B f n a)
--       ((pasting-vertical-coherence-square-maps
--       ( tr P (coherence-cocone-sequential-diagram c n a))
--       ( f' _)
--       ( f' _)
--       ( tr Q (ap finf (coherence-cocone-sequential-diagram c n a)))
--       ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f _ a))
--       ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f _ (map-sequential-diagram A n a)))
--       ( ( tr
--           ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--           ( naturality-map-hom-sequential-diagram B f n a)) ∘
--         ( tr Q (coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))))
--       ( λ q →
--         substitution-law-tr Q finf (coherence-cocone-sequential-diagram c n a) ∙
--         inv (preserves-tr f' (coherence-cocone-sequential-diagram c n a) q))
--       ( ( inv-htpy
--           ( λ q →
--             ( tr-concat
--               ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                 up-c c' f n a)
--               ( _)
--               ( q)) ∙
--             ( tr-concat
--               ( coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))
--               ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a))
--               ( tr Q
--                 ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                   up-c c' f n a)
--                 ( q))) ∙
--             ( substitution-law-tr Q
--               ( map-cocone-sequential-diagram c' (succ-ℕ n))
--               ( naturality-map-hom-sequential-diagram B f n a)))) ∙h
--         ( λ q →
--           ap
--             ( λ p → tr Q p q)
--             ( inv
--               ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a))) ∙h
--         ( tr-concat
--           ( ap finf (coherence-cocone-sequential-diagram c n a))
--           ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--             up-c c' f (succ-ℕ n) (map-sequential-diagram A n a))))) p)


--   totff'∞ : Σ X P → Σ Y Q
--   totff'∞ =
--     map-sequential-colimit-hom-sequential-diagram
--       ( flattening-lemma-sequential-colimit _ P up-c)
--       ( total-cocone-family-cocone-sequential-diagram c' Q)
--       ( totff')

--   pr1A∙ : hom-sequential-diagram ΣAP A
--   pr1A∙ =
--     pr1-total-sequential-diagram
--       ( dependent-sequential-diagram-family-cocone c P)
--   pr1B∙ : hom-sequential-diagram ΣBQ B
--   pr1B∙ =
--     pr1-total-sequential-diagram
--       ( dependent-sequential-diagram-family-cocone c' Q)

--   pr1∘totff' : hom-sequential-diagram ΣAP B
--   pr1∘totff' = comp-hom-sequential-diagram ΣAP ΣBQ B pr1B∙ totff'
--   f∘pr1 : hom-sequential-diagram ΣAP B
--   f∘pr1 = comp-hom-sequential-diagram ΣAP A B f pr1A∙

--   pr1coh∙ : htpy-hom-sequential-diagram B f∘pr1 pr1∘totff'
--   pr1 pr1coh∙ n =
--     refl-htpy
--   pr2 pr1coh∙ n =
--     right-unit-htpy ∙h
--     right-unit-htpy ∙h
--     ( λ x →
--       inv
--         ( ap-pr1-eq-pair-Σ
--           ( naturality-map-hom-sequential-diagram B f n (pr1 x))
--           ( _)))

--   module _
--     (sA :
--       section-descent-data-sequential-colimit
--         ( descent-data-family-cocone-sequential-diagram c P))
--     (sB :
--       section-descent-data-sequential-colimit
--         ( descent-data-family-cocone-sequential-diagram c' Q))
--     where
--     open import foundation.sections

--     -- vertical maps, the "sides" of the cubes
--     sA∙ : hom-sequential-diagram A ΣAP
--     pr1 sA∙ n = map-section-family (pr1 sA n)
--     pr2 sA∙ n a = eq-pair-eq-fiber (pr2 sA n a)
--     sB∙ : hom-sequential-diagram B ΣBQ
--     pr1 sB∙ n = map-section-family (pr1 sB n)
--     pr2 sB∙ n b = eq-pair-eq-fiber (pr2 sB n b)
--     totff'∘sA∙ : hom-sequential-diagram A ΣBQ
--     totff'∘sA∙ = comp-hom-sequential-diagram A ΣAP ΣBQ totff' sA∙
--     sB∙∘f : hom-sequential-diagram A ΣBQ
--     sB∙∘f = comp-hom-sequential-diagram A B ΣBQ sB∙ f
--     -- the unaligned cubes
--     H∙ :
--       htpy-hom-sequential-diagram ΣBQ totff'∘sA∙ sB∙∘f
--     pr1 H∙ n a = eq-pair-eq-fiber {!!}
--     pr2 H∙ = {!!}

--     pr1∙∘sA∙ : hom-sequential-diagram A A
--     pr1∙∘sA∙ = comp-hom-sequential-diagram A ΣAP A pr1A∙ sA∙

--     idA∙ : hom-sequential-diagram A A
--     idA∙ = id-hom-sequential-diagram A
--     idB∙ : hom-sequential-diagram B B
--     idB∙ = id-hom-sequential-diagram B
--     f∘idA∙ : hom-sequential-diagram A B
--     f∘idA∙ = comp-hom-sequential-diagram A A B f idA∙
--     idB∙∘f : hom-sequential-diagram A B
--     idB∙∘f = comp-hom-sequential-diagram A B B idB∙ f
--     refl∙ : htpy-hom-sequential-diagram B f∘idA∙ idB∙∘f
--     pr1 refl∙ = ev-pair refl-htpy
--     pr2 refl∙ n a =
--       right-unit ∙
--       right-unit ∙
--       inv (ap-id (naturality-map-hom-sequential-diagram B f n a))
--     -- the alignment: postcomposing H∙ with pr1coh∙ is homotopic with id
--     ℋ :
--       {!htpy²-hom-sequential-diagram!}
--     ℋ = {!!}

--   _ :
--     totι' up-c
--       ( family-with-descent-data-family-cocone-sequential-diagram c P)
--       ( flattening-lemma-sequential-colimit c P up-c) ~
--     id
--   _ =
--     compute-map-universal-property-sequential-colimit-id
--       ( flattening-lemma-sequential-colimit _ P up-c)

--   _ :
--     coherence-square-maps
--       ( totι' up-c
--         ( family-with-descent-data-family-cocone-sequential-diagram c P)
--         ( flattening-lemma-sequential-colimit c P up-c))
--       ( totff'∞)
--       ( map-Σ Q
--         ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
--         f')
--       ( totι' up-c'
--         ( family-with-descent-data-family-cocone-sequential-diagram c' Q)
--         ( flattening-lemma-sequential-colimit c' Q up-c'))
--   _ =
--     ( compute-map-universal-property-sequential-colimit-id
--       ( flattening-lemma-sequential-colimit c' Q up-c') ·r _) ∙h
--     ( htpy-htpy-out-of-sequential-colimit
--       ( flattening-lemma-sequential-colimit c P up-c)
--       ( concat-htpy-cocone-sequential-diagram
--         ( htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--           ( flattening-lemma-sequential-colimit c P up-c)
--           ( total-cocone-family-cocone-sequential-diagram c' Q)
--           ( totff'))
--         ( ( λ n (a , p) →
--             inv
--               ( eq-pair-Σ
--                 ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c'
--                   ( f)
--                   ( n)
--                   ( a))
--                 refl)) ,
--           {!!}))) ∙h
--     ( _ ·l
--       ( inv-htpy
--         (compute-map-universal-property-sequential-colimit-id
--           ( flattening-lemma-sequential-colimit c P up-c))))

--     -- htpy-htpy-out-of-sequential-colimit
--     --   ( flattening-lemma-sequential-colimit c P up-c)
--     --   ( {!!})
-- ```

-- ```agda
-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : sequential-diagram l1} {X : UU l2}
--   {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   {B : sequential-diagram l3} {Y : UU l4}
--   {c' : cocone-sequential-diagram B Y}
--   (up-c' : universal-property-sequential-colimit c')
--   (f : hom-sequential-diagram A B)
--   where
--   open import foundation.homotopies-morphisms-arrows

--   interm :
--     coherence-square-maps
--       ( id)
--       ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
--       ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
--       ( id)
--   interm =
--     htpy-map-sequential-colimit-htpy-hom-sequential-diagram up-c c'
--       ( refl-htpy-hom-sequential-diagram A B f)

--   preserves-refl-htpy-sequential-colimit :
--     htpy-hom-arrow
--       ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
--       ( map-sequential-colimit-hom-sequential-diagram up-c c' f)
--       ( id , id , interm)
--       ( id , id , refl-htpy)
--   pr1 preserves-refl-htpy-sequential-colimit = refl-htpy
--   pr1 (pr2 preserves-refl-htpy-sequential-colimit) = refl-htpy
--   pr2 (pr2 preserves-refl-htpy-sequential-colimit) =
--     right-unit-htpy ∙h
--     htpy-eq
--       ( ap
--         ( htpy-eq ∘ ap (map-sequential-colimit-hom-sequential-diagram up-c c'))
--         ( is-retraction-map-inv-equiv
--           ( extensionality-hom-sequential-diagram A B f f)
--           ( refl)))
-- ```

-- ```agda
-- module _
--   {l1 l2 l3 l4 : Level}
--   {A : sequential-diagram l1}
--   (B : sequential-diagram l2)
--   (f : hom-sequential-diagram A B)
--   (P : descent-data-sequential-colimit A l3)
--   (Q : descent-data-sequential-colimit B l4)
--   where

--   hom-over-hom : UU (l1 ⊔ l3 ⊔ l4)
--   hom-over-hom =
--     Σ ( (n : ℕ) (a : family-sequential-diagram A n) →
--         family-descent-data-sequential-colimit P n a →
--         family-descent-data-sequential-colimit Q n
--           ( map-hom-sequential-diagram B f n a))
--       ( λ f'n →
--         (n : ℕ) →
--         square-over
--           { Q4 = family-descent-data-sequential-colimit Q (succ-ℕ n)}
--           ( map-sequential-diagram A n)
--           ( map-hom-sequential-diagram B f n)
--           ( map-hom-sequential-diagram B f (succ-ℕ n))
--           ( map-sequential-diagram B n)
--           ( λ {a} → map-family-descent-data-sequential-colimit P n a)
--           ( λ {a} → f'n n a)
--           ( λ {a} → f'n (succ-ℕ n) a)
--           ( λ {a} → map-family-descent-data-sequential-colimit Q n a)
--           ( naturality-map-hom-sequential-diagram B f n))
-- module _
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : sequential-diagram l1} {X : UU l2}
--   {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   {B : sequential-diagram l3} {Y : UU l4}
--   {c' : cocone-sequential-diagram B Y}
--   (up-c' : universal-property-sequential-colimit c')
--   (f : hom-sequential-diagram A B)
--   (P : X → UU l5) (Q : Y → UU l6)
--   where

--   private
--     f∞ : X → Y
--     f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' f
--     DDMO : descent-data-sequential-colimit A (l5 ⊔ l6)
--     pr1 DDMO n a =
--       P (map-cocone-sequential-diagram c n a) →
--       Q (map-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))
--     pr2 DDMO n a =
--       ( equiv-postcomp _
--         ( ( equiv-tr
--             ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--             ( naturality-map-hom-sequential-diagram B f n a)) ∘e
--           ( equiv-tr Q (coherence-cocone-sequential-diagram c' n _)))) ∘e
--       ( equiv-precomp
--         ( inv-equiv (equiv-tr P (coherence-cocone-sequential-diagram c n a)))
--         ( _))

--   sect-over-DDMO-map-over :
--     ((a : X) → P a → Q (f∞ a)) →
--     section-descent-data-sequential-colimit DDMO
--   pr1 (sect-over-DDMO-map-over f∞') n a =
--     ( tr Q
--       ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∘
--     ( f∞' (map-cocone-sequential-diagram c n a))
--   pr2 (sect-over-DDMO-map-over f∞') n a =
--     eq-htpy
--       ( λ p →
--         {!coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a!})

--   sect-over-DDMO-map-over' :
--     ((a : X) → P a → Q (f∞ a)) →
--     section-descent-data-sequential-colimit DDMO
--   sect-over-DDMO-map-over' =
--     {!sect-family-sect-dd-sequential-colimit!}

--   map-over-sect-DDMO :
--     section-descent-data-sequential-colimit DDMO →
--     hom-over-hom B f
--       ( descent-data-family-cocone-sequential-diagram c P)
--       ( descent-data-family-cocone-sequential-diagram c' Q)
--   map-over-sect-DDMO =
--     tot
--       ( λ s →
--         map-Π
--           ( λ n →
--             ( map-implicit-Π
--               ( λ a →
--                 ( concat-htpy
--                   ( inv-htpy
--                     ( ( ( tr
--                           ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--                           ( naturality-map-hom-sequential-diagram B f n a)) ∘
--                         ( tr Q
--                           ( coherence-cocone-sequential-diagram c' n
--                             (map-hom-sequential-diagram B f n a))) ∘
--                         ( s n a)) ·l
--                       ( is-retraction-inv-tr P
--                         ( coherence-cocone-sequential-diagram c n a))))
--                   ( _)) ∘
--                 ( map-equiv
--                   ( equiv-htpy-precomp-htpy-Π _ _
--                     ( equiv-tr P
--                       ( coherence-cocone-sequential-diagram c n a)))) ∘
--                 ( htpy-eq
--                   {f =
--                     ( tr
--                       ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--                       ( naturality-map-hom-sequential-diagram B f n a)) ∘
--                     ( tr Q
--                       ( coherence-cocone-sequential-diagram c' n
--                         ( map-hom-sequential-diagram B f n a))) ∘
--                     ( s n a) ∘
--                     ( tr P (inv (coherence-cocone-sequential-diagram c n a)))}
--                   { s (succ-ℕ n) (map-sequential-diagram A n a)}))) ∘
--             ( implicit-explicit-Π)))

--   map-over-diagram-map-over-colimit :
--     ((a : X) → P a → Q (f∞ a)) →
--     hom-over-hom B f
--       ( descent-data-family-cocone-sequential-diagram c P)
--       ( descent-data-family-cocone-sequential-diagram c' Q)
--   pr1 (map-over-diagram-map-over-colimit f∞') n a =
--     ( tr Q
--       ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a)) ∘
--     ( f∞' (map-cocone-sequential-diagram c n a))
--   pr2 (map-over-diagram-map-over-colimit f∞') n {a} =
--     pasting-vertical-coherence-square-maps
--       ( tr P (coherence-cocone-sequential-diagram c n a))
--       ( f∞' _)
--       ( f∞' _)
--       ( tr Q (ap f∞ (coherence-cocone-sequential-diagram c n a)))
--       ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f _ a))
--       ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f _ (map-sequential-diagram A n a)))
--       ( ( tr
--           ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--           ( naturality-map-hom-sequential-diagram B f n a)) ∘
--         ( tr Q (coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))))
--       ( λ q →
--         substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a) ∙
--         inv (preserves-tr f∞' (coherence-cocone-sequential-diagram c n a) q))
--       ( ( inv-htpy
--           ( λ q →
--             ( tr-concat
--               ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                 up-c c' f n a)
--               ( _)
--               ( q)) ∙
--             ( tr-concat
--               ( coherence-cocone-sequential-diagram c' n (map-hom-sequential-diagram B f n a))
--               ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (naturality-map-hom-sequential-diagram B f n a))
--               ( tr Q
--                 ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                   up-c c' f n a)
--                 ( q))) ∙
--             ( substitution-law-tr Q
--               ( map-cocone-sequential-diagram c' (succ-ℕ n))
--               ( naturality-map-hom-sequential-diagram B f n a)))) ∙h
--         ( λ q →
--           ap
--             ( λ p → tr Q p q)
--             ( inv
--               ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' f n a))) ∙h
--         ( tr-concat
--           ( ap f∞ (coherence-cocone-sequential-diagram c n a))
--           ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--             up-c c' f (succ-ℕ n) (map-sequential-diagram A n a))))

--   abstract
--     triangle-map-over-sect-DDMO :
--       coherence-triangle-maps
--         ( map-over-diagram-map-over-colimit)
--         ( map-over-sect-DDMO)
--         ( sect-over-DDMO-map-over)
--     triangle-map-over-sect-DDMO f∞' =
--       eq-pair-eq-fiber
--         ( eq-htpy
--           ( λ n →
--             eq-htpy-implicit
--               ( λ a →
--                 eq-htpy
--                   ( λ p →
--                     {!!}))))

--     is-equiv-map-over-sect-DDMO :
--       is-equiv map-over-sect-DDMO
--     is-equiv-map-over-sect-DDMO =
--       is-equiv-tot-is-fiberwise-equiv
--         ( λ s →
--           is-equiv-map-Π-is-fiberwise-equiv
--             ( λ n →
--               is-equiv-comp _ _
--                 ( is-equiv-implicit-explicit-Π)
--                 ( is-equiv-map-implicit-Π-is-fiberwise-equiv
--                   ( λ a →
--                     is-equiv-comp _ _
--                       ( funext _ _)
--                       ( is-equiv-comp _ _
--                         ( is-equiv-map-equiv (equiv-htpy-precomp-htpy-Π _ _ _))
--                         ( is-equiv-concat-htpy _ _))))))

--     is-equiv-map-over-diagram-map-over-colimit :
--       is-equiv map-over-diagram-map-over-colimit
--     is-equiv-map-over-diagram-map-over-colimit =
--       {!is-equiv-left-map-triangle
--         ( map-over-diagram-map-over-colimit)
--         ( map-over-sect-DDMO)
--         ( sect-over-DDMO-map-over)
--         ( triangle-map-over-sect-DDMO)
--         ( is-equiv) !}
-- ```

-- ```agda
-- module big-thm
--   {l1 l2 l3 l4 l5 l6 : Level}
--   {A : sequential-diagram l1}
--   {B : sequential-diagram l2}
--   {X : UU l3} {c : cocone-sequential-diagram A X}
--   (up-c : universal-property-sequential-colimit c)
--   {Y : UU l4} {c' : cocone-sequential-diagram B Y}
--   (up-c' : universal-property-sequential-colimit c')
--   (H : hom-sequential-diagram A B)
--   where

--   -- the squares induce a map

--   f∞ : X → Y
--   f∞ = map-sequential-colimit-hom-sequential-diagram up-c c' H

--   Cn : (n : ℕ) →
--     f∞ ∘ map-cocone-sequential-diagram c n ~
--     map-cocone-sequential-diagram c' n ∘ map-hom-sequential-diagram B H n
--   Cn =
--     htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H

--   module _
--     (P : X → UU l5) (Q : Y → UU l6)
--     (f'∞ : {x : X} → P x → Q (f∞ x))
--     where

--     An : ℕ → UU l1
--     An = family-sequential-diagram A
--     Bn : ℕ → UU l2
--     Bn = family-sequential-diagram B
--     an : {n : ℕ} → An n → An (succ-ℕ n)
--     an = map-sequential-diagram A _
--     bn : {n : ℕ} → Bn n → Bn (succ-ℕ n)
--     bn = map-sequential-diagram B _
--     fn : {n : ℕ} → An n → Bn n
--     fn = map-hom-sequential-diagram B H _
--     Hn : {n : ℕ} → bn {n} ∘ fn ~ fn ∘ an
--     Hn = naturality-map-hom-sequential-diagram B H _

--     -- a map-over induces squares-over

--     -- first, the sequences-over:
--     𝒟P : descent-data-sequential-colimit A l5
--     𝒟P = descent-data-family-cocone-sequential-diagram c P
--     𝒫 = dependent-sequential-diagram-descent-data 𝒟P
--     𝒟Q : descent-data-sequential-colimit B l6
--     𝒟Q = descent-data-family-cocone-sequential-diagram c' Q
--     𝒬 = dependent-sequential-diagram-descent-data 𝒟Q

--     Pn : {n : ℕ} → An n → UU l5
--     Pn = family-descent-data-sequential-colimit 𝒟P _
--     Qn : {n : ℕ} → Bn n → UU l6
--     Qn = family-descent-data-sequential-colimit 𝒟Q _

--     pn : {n : ℕ} (a : An n) → Pn a → Pn (an a)
--     pn = map-family-descent-data-sequential-colimit 𝒟P _
--     qn : {n : ℕ} (b : Bn n) → Qn b → Qn (bn b)
--     qn = map-family-descent-data-sequential-colimit 𝒟Q _

--     -- then, the maps over homs
--     f'∞n : {n : ℕ} (a : An n) → Pn a → Qn (fn a)
--     f'∞n a =
--       ( tr Q
--         ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c'
--           ( H)
--           ( _)
--           ( a))) ∘
--       ( f'∞)

--     -- then, the squares-over
--     f'∞n-square-over :
--       {n : ℕ} →
--       square-over {Q4 = Qn} (an {n}) fn fn bn (pn _) (f'∞n _) (f'∞n _) (qn _) Hn
--     f'∞n-square-over {n} {a} =
--       pasting-vertical-coherence-square-maps
--         ( tr P (coherence-cocone-sequential-diagram c n a))
--         ( f'∞)
--         ( f'∞)
--         ( tr Q (ap f∞ (coherence-cocone-sequential-diagram c n a)))
--         ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H _ a))
--         ( tr Q (htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H _ (an a)))
--         ( ( tr
--             ( Q ∘ map-cocone-sequential-diagram c' (succ-ℕ n))
--             ( Hn a)) ∘
--           ( tr Q (coherence-cocone-sequential-diagram c' n (fn a))))
--         ( λ q →
--           substitution-law-tr Q f∞ (coherence-cocone-sequential-diagram c n a) ∙
--           inv (preserves-tr (λ p → f'∞ {p}) (coherence-cocone-sequential-diagram c n a) q))
--         ( ( inv-htpy
--             ( λ q →
--               ( tr-concat
--                 ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                   up-c c' H n a)
--                 ( _)
--                 ( q)) ∙
--               ( tr-concat
--                 ( coherence-cocone-sequential-diagram c' n (fn a))
--                 ( ap (map-cocone-sequential-diagram c' (succ-ℕ n)) (Hn a))
--                 ( tr Q
--                   ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--                     up-c c' H n a)
--                   ( q))) ∙
--               ( substitution-law-tr Q
--                 ( map-cocone-sequential-diagram c' (succ-ℕ n))
--                 ( Hn a)))) ∙h
--           ( λ q →
--             ap
--               ( λ p → tr Q p q)
--               ( inv
--                 ( coherence-htpy-cocone-map-sequential-colimit-hom-sequential-diagram up-c c' H n a))) ∙h
--           ( tr-concat
--             ( ap f∞ (coherence-cocone-sequential-diagram c n a))
--             ( htpy-htpy-cocone-map-sequential-colimit-hom-sequential-diagram
--               up-c c' H (succ-ℕ n) (an a))))

--     thm :
--       (sA : section-dependent-sequential-diagram A 𝒫) →
--       (sB : section-dependent-sequential-diagram B 𝒬) →
--       (S : (n : ℕ) →
--         section-map-over (fn {n}) (f'∞n _)
--           ( map-section-dependent-sequential-diagram A 𝒫 sA n)
--           ( map-section-dependent-sequential-diagram B 𝒬 sB n)) →
--       ((n : ℕ) →
--         section-square-over (an {n}) fn fn bn (pn _) (f'∞n _) (f'∞n _) (qn _)
--           ( map-section-dependent-sequential-diagram A 𝒫 sA n)
--           ( map-section-dependent-sequential-diagram B 𝒬 sB n)
--           ( map-section-dependent-sequential-diagram A 𝒫 sA (succ-ℕ n))
--           ( map-section-dependent-sequential-diagram B 𝒬 sB (succ-ℕ n))
--           ( naturality-map-section-dependent-sequential-diagram A 𝒫 sA n)
--           ( S n)
--           ( S (succ-ℕ n))
--           ( naturality-map-section-dependent-sequential-diagram B 𝒬 sB n)
--           ( Hn)
--           ( f'∞n-square-over)) →
--       section-map-over f∞ f'∞
--         ( sect-family-sect-dd-sequential-colimit up-c P sA)
--         ( sect-family-sect-dd-sequential-colimit up-c' Q sB)
--     thm sA sB S α =
--       map-dependent-universal-property-sequential-colimit
--         ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
--         ( tS ,
--           ( λ n a →
--             map-compute-dependent-identification-eq-value
--               ( f'∞ ∘ sA∞)
--               ( sB∞ ∘ f∞)
--               ( coherence-cocone-sequential-diagram c n a)
--               ( tS n a)
--               ( tS (succ-ℕ n) (an a))
--               ( {!f'∞n-square-over!})))
--       where
--         sA∞ : (x : X) → P x
--         sA∞ = sect-family-sect-dd-sequential-colimit up-c P sA
--         sB∞ : (y : Y) → Q y
--         sB∞ = sect-family-sect-dd-sequential-colimit up-c' Q sB
--         tS :
--           (n : ℕ) →
--           (f'∞ ∘ sA∞ ∘ (map-cocone-sequential-diagram c n)) ~
--           (sB∞ ∘ f∞ ∘ map-cocone-sequential-diagram c n)
--         tS n a =
--           ap f'∞
--             ( pr1
--               ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
--                 ( dependent-universal-property-universal-property-sequential-colimit _ up-c)
--                 ( sA)) n a) ∙
--           map-equiv
--             ( inv-equiv-ap-emb (emb-equiv (equiv-tr Q (Cn n a))))
--             ( S n a ∙
--               inv
--                 ( apd sB∞ (Cn n a) ∙
--                   pr1
--                     ( htpy-dependent-cocone-dependent-universal-property-sequential-colimit
--                       ( dependent-universal-property-universal-property-sequential-colimit _ up-c')
--                       ( sB)) n (fn a)))
-- ```
