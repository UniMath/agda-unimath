# Associativity of composition in Segal types

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.associativity-of-composition-segal-types
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.subtypes
open import foundation.type-arithmetic-dependent-function-types
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps
open import orthogonal-factorization-systems.types-local-at-maps

open import simplicial-type-theory.arrows I
open import simplicial-type-theory.compositions-of-directed-edges I
open import simplicial-type-theory.cubes I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
open import simplicial-type-theory.inequality-directed-interval I
open import simplicial-type-theory.inner-2-horn I
open import simplicial-type-theory.natural-transformations I
open import simplicial-type-theory.segal-types I
open import simplicial-type-theory.standard-simplices I

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.joins-of-types
open import synthetic-homotopy-theory.pushouts
```

</details>

## Construction

### Unfolding square

```agda
subtype-unfolding-square : subtype I2 (Δ¹ × Δ¹)
subtype-unfolding-square (t , s) =
  join-Prop (leq-prop-Δ¹ t s) (leq-prop-Δ¹ s t)

cocone-unfolding-square :
  {l : Level} {A : UU l} → (Δ 2 → A) → (p : Δ¹ × Δ¹) → cocone pr1 pr2 A
pr1 (cocone-unfolding-square f (t , s)) t≤s = f ((s , t) , t≤s)
pr1 (pr2 (cocone-unfolding-square f (t , s))) s≤t = f ((t , s) , s≤t)
pr2 (pr2 (cocone-unfolding-square f (t , s))) (t≤s , s≤t) =
  ap f
    ( eq-type-subtype
      ( subtype-Δ 2)
      ( eq-pair (antisymmetric-leq-Δ¹ s≤t t≤s) (antisymmetric-leq-Δ¹ t≤s s≤t)))

unfolding-square :
  {l : Level} {A : UU l} → (Δ 2 → A) → Δ¹ × Δ¹ → A
unfolding-square {A = A} f (t , s) =
  cogap-join A
    ( cocone-unfolding-square f (t , s))
    ( total-leq-Δ¹')

witness-square-composition-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {x y z : A} → hom▵ x y → hom▵ y z → Δ¹ × Δ¹ → A
witness-square-composition-is-segal is-segal-A f g =
  unfolding-square (witness-composition-is-segal is-segal-A f g)

compute-lower-triangle-unfolding-square :
  {l : Level} {A : UU l} (f : Δ 2 → A) (((t , s) , s≤t) : Δ 2) →
  unfolding-square f (s , t) ＝ f ((t , s) , s≤t)
compute-lower-triangle-unfolding-square {A = A} f ((t , s) , s≤t) =
  ( ap
    ( cogap-join A (cocone-unfolding-square f (s , t)))
    ( eq-is-in-subtype subtype-unfolding-square)) ∙
  ( compute-inl-cogap-join
    ( cocone-unfolding-square f (s , t))
    ( s≤t))

compute-upper-triangle-unfolding-square :
  {l : Level} {A : UU l} (f : Δ 2 → A) (((t , s) , s≤t) : Δ 2) →
  unfolding-square f (t , s) ＝ f ((t , s) , s≤t)
compute-upper-triangle-unfolding-square {A = A} f ((t , s) , s≤t) =
  ( ap
    ( cogap-join A (cocone-unfolding-square f (t , s)))
    ( eq-is-in-subtype subtype-unfolding-square)) ∙
  ( compute-inr-cogap-join
    ( cocone-unfolding-square f (t , s))
    ( s≤t))
```

### Homs between homs

```agda
arrow-in-arrow-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  (f g : arrow▵ A) → (f 1▵ ＝ g 0▵) → arrow▵ (arrow▵ A)
arrow-in-arrow-is-segal is-segal-A f g p t s =
  unfolding-square
    ( witness-composition-horn-is-segal is-segal-A (rec-arrow-Λ²₁ f g p))
    ( t , s)

eq-source-arrow-in-arrow-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  (f g : arrow▵ A) (p : f 1▵ ＝ g 0▵) →
  arrow-in-arrow-is-segal is-segal-A f g p 0▵ ＝ f
eq-source-arrow-in-arrow-is-segal is-segal-A f g p =
  eq-htpy
    ( λ s →
      ( compute-lower-triangle-unfolding-square
        ( witness-composition-horn-is-segal is-segal-A (rec-arrow-Λ²₁ f g p))
        ( (s , 0▵) , min-leq-Δ¹)) ∙
      ( compute-first-witness-composition-arrow
          f g p (composition-arrow-is-segal is-segal-A f g p) s))

hom-in-hom-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {x y z : A} (f : hom▵ x y) (g : hom▵ y z) → hom▵ (arrow-hom▵ f) (arrow-hom▵ g)
pr1 (hom-in-hom-is-segal is-segal-A f g) t s =
  witness-square-composition-is-segal is-segal-A f g (t , s)
pr1 (pr2 (hom-in-hom-is-segal is-segal-A f g)) =
  eq-htpy
    ( λ s →
      ( compute-lower-triangle-unfolding-square
        ( witness-composition-is-segal is-segal-A f g)
        ( (s , 0▵) , min-leq-Δ¹)) ∙
      ( compute-first-witness-composition
          f g (composition-is-segal is-segal-A f g) s))
pr2 (pr2 (hom-in-hom-is-segal is-segal-A f g)) =
  eq-htpy
    ( λ s →
      ( compute-upper-triangle-unfolding-square
        ( witness-composition-is-segal is-segal-A f g)
        ( (1▵ , s) , max-leq-Δ¹)) ∙
      ( compute-second-witness-composition
          f g (composition-is-segal is-segal-A f g) s))

compute-diagonal-witness-square-composition-is-segal :
  { l : Level} {A : UU l}
  ( is-segal-A : is-segal A)
  { x y z : A} (f : hom▵ x y) (g : hom▵ y z) →
  ( t : Δ¹) →
  ( arrow-hom▵ (hom-in-hom-is-segal is-segal-A f g) t t) ＝
  ( arrow-hom▵ (comp-is-segal is-segal-A f g) t)
compute-diagonal-witness-square-composition-is-segal is-segal-A f g t =
    compute-upper-triangle-unfolding-square
      ( witness-composition-is-segal is-segal-A f g)
      ( (t , t) , refl-leq-Δ¹)
```

### The associativity tetrahedron

```agda
witness-asociative-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} → hom▵ w x → hom▵ x y → hom▵ y z →
  Δ 2 → arrow▵ A
witness-asociative-is-segal is-segal-A f g h =
  witness-composition-is-segal
    ( is-segal-arrow is-segal-A)
    ( hom-in-hom-is-segal is-segal-A f g)
    ( hom-in-hom-is-segal is-segal-A g h)

-- hom▵²-asociative-is-segal :
--   {l : Level} {A : UU l} (is-segal-A : is-segal A)
--   {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
--   ( hom-in-hom-is-segal is-segal-A f g)
--   ( hom-in-hom-is-segal is-segal-A g h)
--   ( comp-is-segal (is-segal-arrow is-segal-A)
--     (hom-in-hom-is-segal is-segal-A f g)
--     (hom-in-hom-is-segal is-segal-A g h))
-- pr1 (hom▵²-asociative-is-segal is-segal-A f g h) =
--   witness-asociative-is-segal is-segal-A f g h
-- pr2 (hom▵²-asociative-is-segal is-segal-A f g h) = {!   !}

tetrahedron-associative-Segal :
  {l : Level} {A : UU l}
  (is-segal-A : is-segal A)
  {w x y z : A} → hom▵ w x → hom▵ x y → hom▵ y z →
  Δ 3 → A
tetrahedron-associative-Segal is-segal-A f g h ((t , s , r) , s≤t , r≤s) =
  witness-asociative-is-segal
    is-segal-A f g h ((t , r) , transitive-leq-Δ¹ s≤t r≤s) s
```

### The triple composite

```agda
arrow-triple-comp-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} → hom▵ w x → hom▵ x y → hom▵ y z → arrow▵ A
arrow-triple-comp-is-segal is-segal-A f g h t =
  tetrahedron-associative-Segal is-segal-A f g h
    ( (t , t , t) , refl-leq-Δ¹ , refl-leq-Δ¹)

triple-comp-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} → hom▵ w x → hom▵ x y → hom▵ y z → hom▵ w z
pr1 (triple-comp-is-segal is-segal-A f g h) =
  arrow-triple-comp-is-segal is-segal-A f g h
pr1 (pr2 (triple-comp-is-segal is-segal-A f g h)) =
  ( ap
    ( λ p →
      witness-composition-is-segal
        ( is-segal-arrow is-segal-A)
        ( hom-in-hom-is-segal is-segal-A f g)
        ( hom-in-hom-is-segal is-segal-A g h)
        ( (0▵ , 0▵) , p) 0▵)
    ( eq-is-prop
        ( is-prop-leq-Δ¹)
        { transitive-leq-Δ¹ refl-leq-Δ¹ refl-leq-Δ¹}
        { refl-leq-Δ¹})) ∙
  ( ( ap
      ( λ f → f 0▵)
      ( compute-first-witness-composition
        ( hom-in-hom-is-segal is-segal-A f g)
        ( hom-in-hom-is-segal is-segal-A g h)
        ( composition-is-segal
          ( is-segal-arrow is-segal-A)
          ( hom-in-hom-is-segal is-segal-A f g)
          ( hom-in-hom-is-segal is-segal-A g h))
        ( 0▵))) ∙
    ( htpy-eq (eq-source-hom▵ (hom-in-hom-is-segal is-segal-A f g)) 0▵) ∙
    ( eq-source-hom▵ f))
pr2 (pr2 (triple-comp-is-segal is-segal-A f g h)) =
  ( ap
    ( λ p →
      witness-composition-is-segal
        ( is-segal-arrow is-segal-A)
        ( hom-in-hom-is-segal is-segal-A f g)
        ( hom-in-hom-is-segal is-segal-A g h)
        ( (1▵ , 1▵) , p) 1▵)
    ( eq-is-prop
      ( is-prop-leq-Δ¹)
      { transitive-leq-Δ¹ refl-leq-Δ¹ refl-leq-Δ¹}
      { refl-leq-Δ¹})) ∙
  ( ap
    ( λ f → f 1▵)
    ( compute-second-witness-composition
      ( hom-in-hom-is-segal is-segal-A f g)
      ( hom-in-hom-is-segal is-segal-A g h)
      ( composition-is-segal
        ( is-segal-arrow is-segal-A)
        ( hom-in-hom-is-segal is-segal-A f g)
        ( hom-in-hom-is-segal is-segal-A g h))
      ( 1▵))) ∙
  ( htpy-eq (eq-target-hom▵ (hom-in-hom-is-segal is-segal-A g h)) 1▵) ∙
  ( eq-target-hom▵ h)
```

### Left witness

```text
left-witness-associative-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
  Δ 2 → A
left-witness-associative-is-segal is-segal-A f g h ((t , s) , s≤t) =
  tetrahedron-associative-Segal is-segal-A f g h
    ( (t , t , s) , refl-leq-Δ¹ , s≤t)

is-left-composite-arrow-triple-comp-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
  is-composite-arrow
    ( arrow-hom▵ (comp-is-segal is-segal-A f g))
    ( arrow-hom▵ h)
    ( eq-source-target-hom (comp-is-segal is-segal-A f g) h)
    ( arrow-triple-comp-is-segal is-segal-A f g h)
pr1 (pr1 (is-left-composite-arrow-triple-comp-is-segal is-segal-A f g h)) =
  left-witness-associative-is-segal is-segal-A f g h
pr2 (pr1 (is-left-composite-arrow-triple-comp-is-segal is-segal-A f g h))
  ( (t , s) , r) =
  cogap-join
    ( _)
    ( ( λ
        { refl →
          ( compute-inl-rec-arrow-Λ²₁
            ( arrow-hom▵ (comp-is-segal is-segal-A f g))
            ( arrow-hom▵ h)
            ( _)
            ( t)) ∙
          ( ( inv
              ( compute-diagonal-witness-square-composition-is-segal
                ( is-segal-A) f g t)) ∙
            ( inv
              ( htpy-eq
                  ( compute-first-witness-composition-is-segal
                    ( is-segal-arrow is-segal-A)
                    ( hom-in-hom-is-segal is-segal-A f g)
                    ( hom-in-hom-is-segal is-segal-A g h)
                    ( t))
                  ( t))))}) ,
      ( λ
        { refl →
          ( compute-inr-rec-arrow-Λ²₁
            ( arrow-hom▵ (comp-is-segal is-segal-A f g))
            ( arrow-hom▵ h)
            ( _)
            ( s)) ∙
          ( ( inv
              ( ( compute-lower-triangle-unfolding-square
                  ( witness-composition-is-segal is-segal-A g h)
                  ( (1▵ , s) , max-leq-Δ¹)) ∙
                ( compute-second-witness-composition-is-segal is-segal-A g h
                  ( s))))∙
            ( inv
              ( htpy-eq
                  ( compute-second-witness-composition-is-segal
                    ( is-segal-arrow is-segal-A)
                    ( hom-in-hom-is-segal is-segal-A f g)
                    ( hom-in-hom-is-segal is-segal-A g h)
                    ( s))
                  ( 1▵))))}) ,
      ( λ
        { (refl , refl) →
        equational-reasoning
          ( ( ap
              ( λ r' → rec-arrow-Λ²₁ _ (arrow-hom▵ h) _ ((1▵ , 0▵) , r'))
              ( eq-is-in-subtype subtype-Λ²₁)) ∙
            ( compute-inl-cogap-join _ refl)) ∙
          ( ( inv
              ( compute-diagonal-witness-square-composition-is-segal
                ( is-segal-A) f g 1▵)) ∙
            ( inv
              ( htpy-eq
                  ( compute-first-witness-composition-is-segal
                    ( is-segal-arrow is-segal-A)
                    ( hom-in-hom-is-segal is-segal-A f g)
                    ( hom-in-hom-is-segal is-segal-A g h)
                    ( 1▵))
                  ( 1▵))))
          ＝ {!   !}
          by ap (_∙ _) {! inv (right-transpose-eq ? ? ? 1▵) !}
          ＝ {!   !} by {!   !}
          ＝ {!   !} by {!   !}
          ＝ {!   !} by {!   !}
          ＝ {!   !} by {!   !}
          ＝ {!   !}
            -- ( compute-inr-rec-arrow-Λ²₁
            --   ( pr1 (comp-is-segal is-segal-A f g))
            --   ( pr1 h)
            --   ( eq-source-target-hom (comp-is-segal is-segal-A f g) h)
            --   ( 0▵)) ∙
            -- ( inv
            --   ( ( htpy-eq
            --       ( compute-second-witness-composition-is-segal
            --         ( is-segal-arrow is-segal-A)
            --         ( hom-in-hom-is-segal is-segal-A f g)
            --         ( hom-in-hom-is-segal is-segal-A g h)
            --         ( 0▵))
            --       ( 1▵)) ∙
            --     ( compute-lower-triangle-unfolding-square
            --       ( witness-composition-is-segal is-segal-A g h)
            --       ( (1▵ , 0▵) , max-leq-Δ¹)) ∙
            --     ( compute-second-witness-composition-is-segal is-segal-A g h 0▵)))
          by {!   !}
          }))
    ( r)
pr2 (is-left-composite-arrow-triple-comp-is-segal is-segal-A f g h) = {!   !}

is-left-composite-triple-comp-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
  is-composite-hom
    ( comp-is-segal is-segal-A f g)
    ( h)
    ( triple-comp-is-segal is-segal-A f g h)
pr1 (pr1 (is-left-composite-triple-comp-is-segal is-segal-A f g h)) =
  left-witness-associative-is-segal is-segal-A f g h
pr2 (pr1 (is-left-composite-triple-comp-is-segal is-segal-A f g h)) =
  pr2 (pr1 (is-left-composite-arrow-triple-comp-is-segal is-segal-A f g h))
pr2 (is-left-composite-triple-comp-is-segal is-segal-A f g h) =
  eq-htpy-hom
    ( composite-composition
      ( comp-is-segal is-segal-A f g)
      ( h)
      ( pr1 (is-left-composite-triple-comp-is-segal is-segal-A f g h)))
    ( triple-comp-is-segal is-segal-A f g h)
    ( htpy-eq
      ( pr2 (is-left-composite-arrow-triple-comp-is-segal is-segal-A f g h)) ,
      {!   !})

arrow-left-associative-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
  ( arrow-hom▵ (comp-is-segal is-segal-A (comp-is-segal is-segal-A f g) h)) ＝
  ( arrow-triple-comp-is-segal is-segal-A f g h)
arrow-left-associative-is-segal is-segal-A f g h =
  unique-composite-arrow-is-segal
    ( is-segal-A)
    ( arrow-hom▵ (comp-is-segal is-segal-A f g))
    ( arrow-hom▵ h)
    ( eq-source-target-hom (comp-is-segal is-segal-A f g) h)
    ( arrow-triple-comp-is-segal is-segal-A f g h)
    ( is-left-composite-arrow-triple-comp-is-segal is-segal-A f g h)

left-associative-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
  ( comp-is-segal is-segal-A (comp-is-segal is-segal-A f g) h) ＝
  ( triple-comp-is-segal is-segal-A f g h)
left-associative-is-segal is-segal-A f g h =
  unique-composite-is-segal is-segal-A
    ( comp-is-segal is-segal-A f g)
    ( h)
    ( triple-comp-is-segal is-segal-A f g h)
    ( is-left-composite-triple-comp-is-segal is-segal-A f g h)
```

### Right witness

```agda
right-witness-associative-is-segal :
  {l : Level} {A : UU l} (is-segal-A : is-segal A)
  {w x y z : A} (f : hom▵ w x) (g : hom▵ x y) (h : hom▵ y z) →
  Δ 2 → A
right-witness-associative-is-segal is-segal-A f g h ((t , s) , s≤t) =
  tetrahedron-associative-Segal is-segal-A f g h
    ( (t , s , s) , s≤t , refl-leq-Δ¹)
```
