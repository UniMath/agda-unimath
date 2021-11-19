{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

module book.b-systems where

open import book.27-sequences public

module B where
  
  record system (l1 l2 : Level) : UU (lsuc l1 ⊔ lsuc l2)
    where
    field
      type    : ℕ → UU l1
      element : ℕ → UU l2
      ft      : {n : ℕ} → type (succ-ℕ n) → type n
      ∂       : {n : ℕ} → element n → type n

  -- We define the interpretations of the judgments of type theory

  data precontext {l1 l2 : Level} (A : system l1 l2) : ℕ → UU (lsuc l1)
    where
    empty-context     : precontext A zero-ℕ
    extension-context : {n : ℕ} (Γ : precontext A n) → system.type A n →
                        precontext A (succ-ℕ n)
  
  head-precontext :
    {l1 l2 : Level} {A : system l1 l2} {n : ℕ} →
    precontext A (succ-ℕ n) → system.type A n
  head-precontext (extension-context Γ X) = X
  
  data is-context-precontext {l1 l2 : Level} {A : system l1 l2} :
    {n : ℕ} (Γ : precontext A n) → UU (lsuc l1)
    where
    is-context-empty-context :
      is-context-precontext empty-context
    is-context-extension-closed-type-ctx :
      (X : system.type A zero-ℕ) →
      is-context-precontext (extension-context empty-context X)
    is-context-extenison-ctx :
      {n : ℕ} {Γ : precontext A (succ-ℕ n)} {X : system.type A (succ-ℕ n)}
      {Y : system.type A (succ-ℕ (succ-ℕ n))} →
      is-context-precontext (extension-context Γ X) →
      Id (system.ft A Y) X →
      is-context-precontext (extension-context (extension-context Γ X) Y)
  
  context : {l1 l2 : Level} (A : system l1 l2) (n : ℕ) → UU (lsuc l1)
  context A n = Σ (precontext A n) is-context-precontext

  precontext-context :
    {l1 l2 : Level} {A : system l1 l2} {n : ℕ} →
    context A n → precontext A n
  precontext-context Γ = pr1 Γ

  is-context-precontext-context :
    {l1 l2 : Level} {A : system l1 l2} {n : ℕ} →
    (Γ : context A n) → is-context-precontext (precontext-context Γ)
  is-context-precontext-context Γ = pr2 Γ
  
  head-context :
    {l1 l2 : Level} (A : system l1 l2) {n : ℕ} (Γ : context A (succ-ℕ n)) →
    system.type A n
  head-context A (pair (extension-context Γ X) p) = X
  
  type-in-context :
    {l1 l2 : Level} (A : system l1 l2) {n : ℕ} (Γ : context A n) → UU l1
  type-in-context A {zero-ℕ} Γ = system.type A zero-ℕ
  type-in-context A {succ-ℕ n} Γ = fib (system.ft A) (head-context A Γ)

  type-type-in-context :
    {l1 l2 : Level} {A : system l1 l2} {n : ℕ} (Γ : context A n) →
    type-in-context A Γ → system.type A n
  type-type-in-context {n = zero-ℕ} Γ A = A
  type-type-in-context {n = succ-ℕ n} Γ A = pr1 A
  
  judgmental-eq-type-in-context :
    {l1 l2 : Level} (A : system l1 l2) {n : ℕ} (Γ : context A n)
    (X Y : type-in-context A Γ) → UU l1
  judgmental-eq-type-in-context A Γ X Y =
    Id (type-type-in-context Γ X) (type-type-in-context Γ Y)
  
  element-in-context :
    {l1 l2 : Level} (A : system l1 l2) {n : ℕ} (Γ : context A n)
    (X : type-in-context A Γ) → UU (l1 ⊔ l2)
  element-in-context A {zero-ℕ} Γ X = fib (system.∂ A) X
  element-in-context A {succ-ℕ n} Γ X =
    fib (system.∂ A) (type-type-in-context Γ X)

  element-element-in-context :
    {l1 l2 : Level} {A : system l1 l2} {n : ℕ} (Γ : context A n)
    (X : type-in-context A Γ) →
    element-in-context A Γ X → system.element A n
  element-element-in-context {n = zero-ℕ} Γ X a = pr1 a
  element-element-in-context {n = succ-ℕ n} Γ X a = pr1 a

  judgmental-equality-element-in-context :
    {l1 l2 : Level} {A : system l1 l2} {n : ℕ} (Γ : context A n)
    (X : type-in-context A Γ) (a b : element-in-context A Γ X) →
    UU l2
  judgmental-equality-element-in-context Γ X a b =
    Id (element-element-in-context Γ X a) (element-element-in-context Γ X b)

  -- We define the slice of a B-structure

  iterate-using-add-system-ft :
    {l1 l2 : Level} (A : system l1 l2) (n k : ℕ) {m : ℕ}
    (p : Id (add-ℕ n k) m) → system.type A m → system.type A n
  iterate-using-add-system-ft A n zero-ℕ refl X = X
  iterate-using-add-system-ft A n (succ-ℕ k) refl X =
    iterate-using-add-system-ft A n k refl (system.ft A X)

  iterate-using-leq-system-ft :
    {l1 l2 : Level} (A : system l1 l2) (n : ℕ) {m : ℕ} (p : n ≤-ℕ m) →
    system.type A m → system.type A n
  iterate-using-leq-system-ft A n {m} p X =
    iterate-using-add-system-ft A n
      ( dist-ℕ n m)
      ( is-additive-right-inverse-dist-ℕ n m p) X
    
  iterate-system-ft :
    {l1 l2 : Level} (A : system l1 l2) (n k : ℕ) →
    system.type A (add-ℕ n k) → system.type A n
  iterate-system-ft A n k = iterate-using-add-system-ft A n k refl

{-
  slice-system :
    {l1 l2 : Level} (A : system l1 l2) {n : ℕ} → context A n →
    system l1 (l1 ⊔ l2)
  slice-system A (pair empty-context p) = {!A!}
  slice-system A (pair (extension-context Γ x) p) = {!!}
-}

--   slice-system :
--     {l1 l2 : Level} (A : system l1 l2) {n : ℕ} → system.type A n →
--     system l1 (l1 ⊔ l2)
--   system.type (slice-system A {n} X) m =
--     fib (iterate-system-ft A n (succ-ℕ m)) X
--   system.element (slice-system A {n} X) m =
--     fib (iterate-system-ft A n (succ-ℕ m) ∘ system.∂ A) X
--   system.ft (slice-system A {n} X) {m} =
--     fib-triangle' (iterate-system-ft A n (succ-ℕ m)) (system.ft A) X
--   system.∂ (slice-system A {n} X) {m} =
--     fib-triangle' (iterate-system-ft A n (succ-ℕ m)) (system.∂ A) X

--   slice-system-ft :
--     {l1 l2 : Level} (A : system l1 l2) {n : ℕ} → system.type A n →
--     system l1 (l1 ⊔ l2)
--   system.type (slice-system-ft A {n} X) m = fib (iterate-system-ft A n m) X
--   system.element (slice-system-ft A {n} X) m =
--     fib (iterate-system-ft A n m ∘ system.∂ A) X
--   system.ft (slice-system-ft A {n} X) {m} =
--     fib-triangle' (iterate-system-ft A n m) (system.ft A) X
--   system.∂ (slice-system-ft A {n} X) {m} =
--     fib-triangle' (iterate-system-ft A n m) (system.∂ A) X

--   record hom-system
--     {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--     where
--     field
--       type    : {n : ℕ} → system.type A n → system.type B n
--       element : {n : ℕ} → system.element A n  → system.element B n
--       ft      : {n : ℕ} (X : system.type A (succ-ℕ n)) →
--                 Id (type (system.ft A X)) (system.ft B (type X))
--       ∂       : {n : ℕ} (x : system.element A n) →
--                 Id (type (system.∂ A x)) (system.∂ B (element x))

--   slice-hom-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
--     (f : hom-system A B) {n : ℕ} (X : system.type A n) →
--     hom-system (slice-system A X) (slice-system B (hom-system.type f X))
--   hom-system.type (slice-hom-system f X) =
--     fib-square {!!} {!!} {!!} {!!}
--   hom-system.element (slice-hom-system f X) = {!!}
--   hom-system.ft (slice-hom-system f X) = {!!}
--   hom-system.∂ (slice-hom-system f X) = {!!}

-- {-

--   record fibered-system {l1 l2 : Level} (l3 l4 : Level) (A : system l1 l2) :
--     UU (l1 ⊔ l2 ⊔ lsuc l3 ⊔ lsuc l4)
--     where
--     field
--       type    : {n : ℕ} → system.type A n → UU l3
--       element : {n : ℕ} → system.element A n → UU l4
--       ft      : {n : ℕ} {X : system.type A (succ-ℕ n)} →
--                 type X → type (system.ft A X)
--       ∂       : {n : ℕ} {x : system.element A n} →
--                 element x → type (system.∂ A x)

--   iterate-using-add-fibered-ft :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
--     (n k : ℕ) {m : ℕ} (p : Id (add-ℕ n k) m) {X : system.type A m} → 
--     fibered-system.type B X →
--     fibered-system.type B (iterate-using-add-system-ft A n k p X)
--   iterate-using-add-fibered-ft B n zero-ℕ refl Y = Y
--   iterate-using-add-fibered-ft B n (succ-ℕ k) refl Y =
--     iterate-using-add-fibered-ft B n k refl (fibered-system.ft B Y)

--   iterate-using-leq-fibered-ft :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
--     (n : ℕ) {m : ℕ} (p : n ≤-ℕ m) {X : system.type A m} →
--     fibered-system.type B X →
--     fibered-system.type B (iterate-using-leq-system-ft A n p X)
--   iterate-using-leq-fibered-ft B n {m} p Y =
--     iterate-using-add-fibered-ft B n (dist-ℕ n m) (leq-dist-ℕ n m p) Y

--   iterate-fibered-ft' :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
--     (n k : ℕ) → {X : system.type A (add-ℕ n k)} →
--     fibered-system.type B X →
--     fibered-system.type B (iterate-system-ft A n k X)
--   iterate-fibered-ft' B n k Y =
--     iterate-using-add-fibered-ft B n k refl Y

--   slice-fibered-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
--     {n : ℕ} {X : system.type A n} (Y : fibered-system.type B X) →
--     fibered-system l3 l4 (slice-system A X)
--   fibered-system.type (slice-fibered-system B {n} {X} Y) (pair X' p) =
--     Σ {!!} {!!}
--   fibered-system.element (slice-fibered-system B {n} {X} Y) = {!!}
--   fibered-system.ft (slice-fibered-system B {n} {X} Y) = {!!}
--   fibered-system.∂ (slice-fibered-system B {n} {X} Y) = {!!}
-- -}


-- {-
--   fibered-system.type
--     ( slice-fibered-system {A = A} B {n}
--       {.(iterate-using-add-system-ft A n m refl (system.ft A X'))} Y)
--       {m} (pair X' refl) =
--     fib (iterate-using-add-fibered-ft B n m {add-ℕ n m} refl) Y
-- -}

-- {-
--   slice-fibered-system-ft :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A)
--     {n : ℕ} {X : system.type A n} (Y : fibered-system.type B X) →
--     fibered-system l3 l4 (slice-system-ft A X)
--   fibered-system.type (slice-fibered-system-ft B Y) = fibered-system.type B
--   fibered-system.element (slice-fibered-system-ft B Y) =
--     fibered-system.element B
--   fibered-system.ft (slice-fibered-system-ft B Y) = fibered-system.ft B
--   fibered-system.∂ (slice-fibered-system-ft B Y) = fibered-system.∂ B

--   record section-system
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A) :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--     where
--     field
--       type    : {n : ℕ} (X : system.type A n) → fibered-system.type B X
--       element : {n : ℕ} (x : system.element A n) → fibered-system.element B x
--       ft      : {n : ℕ} (X : system.type A (succ-ℕ n)) →
--                 Id (fibered-system.ft B (type X)) (type (system.ft A X))
--       ∂       : {n : ℕ} (x : system.element A n) →
--                 Id (fibered-system.∂ B (element x)) (type (system.∂ A x))

--   slice-section-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
--     (f : section-system B) {n : ℕ} (X : system.type A n) →
--     section-system (slice-fibered-system B (section-system.type f X))
--   section-system.type (slice-section-system f X) = section-system.type f
--   section-system.element (slice-section-system f X) = section-system.element f
--   section-system.ft (slice-section-system f X) = section-system.ft f
--   section-system.∂ (slice-section-system f X) = section-system.∂ f

--   slice-section-system-ft :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
--     (f : section-system B) {n : ℕ} (X : system.type A n) →
--     section-system (slice-fibered-system-ft B (section-system.type f X))
--   section-system.type (slice-section-system-ft f X) =
--     section-system.type f
--   section-system.element (slice-section-system-ft f X) =
--     section-system.element f
--   section-system.ft (slice-section-system-ft f X) = section-system.ft f
--   section-system.∂ (slice-section-system-ft f X) = section-system.∂ f

--   record bifibered-system
--     {l1 l2 l3 l4 l5 l6 : Level} (l7 l8 : Level) {A : system l1 l2}
--     (B : fibered-system l3 l4 A) (C : fibered-system l5 l6 A) :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5 ⊔ l6 ⊔ lsuc l7 ⊔ lsuc l8)
--     where
--     field
--       type    : {n : ℕ} {X : system.type A n} →
--                 fibered-system.type B X → fibered-system.type C X → UU l7
--       element : {n : ℕ} {x : system.element A n} →
--                 fibered-system.element B x → fibered-system.element C x → UU l8
--       ft      : {n : ℕ} {X : system.type A (succ-ℕ n)}
--                 {Y : fibered-system.type B X} {Z : fibered-system.type C X} →
--                 type Y Z → type (fibered-system.ft B Y) (fibered-system.ft C Z)
--       ∂       : {n : ℕ} {x : system.element A n}
--                 {y : fibered-system.element B x}
--                 {z : fibered-system.element C x} → element y z →
--                 type (fibered-system.∂ B y) (fibered-system.∂ C z)

--   slice-bifibered-system :
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
--     {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
--     (D : bifibered-system l7 l8 B C) {n : ℕ} {X : system.type A n}
--     {Y : fibered-system.type B X} {Z : fibered-system.type C X} →
--     (W : bifibered-system.type D Y Z) → 
--     bifibered-system l7 l8
--       ( slice-fibered-system B Y)
--       ( slice-fibered-system C Z)
--   bifibered-system.type (slice-bifibered-system D W) =
--     bifibered-system.type D
--   bifibered-system.element (slice-bifibered-system D W) =
--     bifibered-system.element D
--   bifibered-system.ft (slice-bifibered-system D W) =
--     bifibered-system.ft D
--   bifibered-system.∂ (slice-bifibered-system D W) =
--     bifibered-system.∂ D

--   slice-bifibered-system-ft :
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
--     {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
--     (D : bifibered-system l7 l8 B C) {n : ℕ} {X : system.type A n}
--     {Y : fibered-system.type B X} {Z : fibered-system.type C X}
--     (W : bifibered-system.type D Y Z) →
--     bifibered-system l7 l8
--       ( slice-fibered-system-ft B Y)
--       ( slice-fibered-system-ft C Z)
--   bifibered-system.type (slice-bifibered-system-ft D W) =
--     bifibered-system.type D
--   bifibered-system.element (slice-bifibered-system-ft D W) =
--     bifibered-system.element D
--   bifibered-system.ft (slice-bifibered-system-ft D W) =
--     bifibered-system.ft D
--   bifibered-system.∂ (slice-bifibered-system-ft D W) =
--     bifibered-system.∂ D

--   record section-fibered-system
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
--     {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
--     (D : bifibered-system l7 l8 B C) (f : section-system C) :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
--     where
--     field
--       type    : {n : ℕ} {X : system.type A n} (Y : fibered-system.type B X) →
--                 bifibered-system.type D Y (section-system.type f X)
--       element : {n : ℕ} {x : system.element A n}
--                 (y : fibered-system.element B x) →
--                 bifibered-system.element D y (section-system.element f x)
--       ft      : {n : ℕ} {X : system.type A (succ-ℕ n)}
--                 (Y : fibered-system.type B X) →
--                 Id ( tr ( bifibered-system.type D (fibered-system.ft B Y))
--                         ( section-system.ft f X)
--                         ( bifibered-system.ft D (type Y)))
--                    ( type (fibered-system.ft B Y))
--       ∂       : {n : ℕ} {x : system.element A n}
--                 (y : fibered-system.element B x) →
--                 Id ( tr ( bifibered-system.type D (fibered-system.∂ B y))
--                         ( section-system.∂ f x)
--                         ( bifibered-system.∂ D (element y)))
--                    ( type (fibered-system.∂ B y))

--   slice-section-fibered-system :
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
--     {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
--     (D : bifibered-system l7 l8 B C) {f : section-system C}
--     (g : section-fibered-system D f) {n : ℕ} {X : system.type A n}
--     (Y : fibered-system.type B X) →
--     section-fibered-system
--       ( slice-bifibered-system D (section-fibered-system.type g Y))
--       ( slice-section-system f X)
--   section-fibered-system.type (slice-section-fibered-system D g Y) =
--     section-fibered-system.type g
--   section-fibered-system.element (slice-section-fibered-system D g Y) =
--     section-fibered-system.element g
--   section-fibered-system.ft (slice-section-fibered-system D g Y) =
--     section-fibered-system.ft g
--   section-fibered-system.∂ (slice-section-fibered-system D g Y) =
--     section-fibered-system.∂ g

--   slice-section-fibered-system-ft :
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
--     {B : fibered-system l3 l4 A} {C : fibered-system l5 l6 A}
--     (D : bifibered-system l7 l8 B C) {f : section-system C}
--     (g : section-fibered-system D f) {n : ℕ} {X : system.type A n}
--     (Y : fibered-system.type B X) →
--     section-fibered-system
--       ( slice-bifibered-system-ft D (section-fibered-system.type g Y))
--       ( slice-section-system-ft f X)
--   section-fibered-system.type (slice-section-fibered-system-ft D g Y) =
--     section-fibered-system.type g
--   section-fibered-system.element (slice-section-fibered-system-ft D g Y) =
--     section-fibered-system.element g
--   section-fibered-system.ft (slice-section-fibered-system-ft D g Y) =
--     section-fibered-system.ft g
--   section-fibered-system.∂ (slice-section-fibered-system-ft D g Y) =
--     section-fibered-system.∂ g

--   Eq-fibered-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
--     (f g : section-system B) → fibered-system l3 l4 A
--   fibered-system.type (Eq-fibered-system f g) {n} X =
--     Id (section-system.type f X) (section-system.type g X)
--   fibered-system.element (Eq-fibered-system f g) {n} x =
--     Id (section-system.element f x) (section-system.element g x)
--   fibered-system.ft (Eq-fibered-system {B = B} f g) {n} {X} p =
--     ( inv (section-system.ft f X)) ∙
--     ( ( ap (fibered-system.ft B) p) ∙
--       ( section-system.ft g X))
--   fibered-system.∂ (Eq-fibered-system {B = B} f g) {n} {x} p =
--     ( inv (section-system.∂ f x)) ∙
--       ( ( ap (fibered-system.∂ B) p) ∙
--         ( section-system.∂ g x))

--   htpy-section-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
--     (f g : section-system B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--   htpy-section-system f g = section-system (Eq-fibered-system f g)

--   refl-htpy-section-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
--     (f : section-system B) → htpy-section-system f f
--   section-system.type (refl-htpy-section-system f) = refl-htpy
--   section-system.element (refl-htpy-section-system f) = refl-htpy
--   section-system.ft (refl-htpy-section-system f) X =
--     left-inv (section-system.ft f X)
--   section-system.∂ (refl-htpy-section-system f) x =
--     left-inv (section-system.∂ f x)

--   constant-fibered-system :
--     {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
--     fibered-system l3 l4 A
--   fibered-system.type (constant-fibered-system A B) {n} X = system.type B n
--   fibered-system.element (constant-fibered-system A B) {n} x =
--     system.element B n
--   fibered-system.ft (constant-fibered-system A B) = system.ft B
--   fibered-system.∂ (constant-fibered-system A B) = system.∂ B

--   hom-system :
--     {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) →
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--   hom-system A B = section-system (constant-fibered-system A B)

--   slice-hom-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
--     (f : hom-system A B) {n : ℕ} (X : system.type A n) →
--     hom-system (slice-system A X) (slice-system B (section-system.type f X))
--   slice-hom-system f X = slice-section-system f X

--   id-hom-system :
--     {l1 l2 : Level} (A : system l1 l2) → hom-system A A
--   section-system.type (id-hom-system A) = id
--   section-system.element (id-hom-system A) = id
--   section-system.ft (id-hom-system A) = refl-htpy
--   section-system.∂ (id-hom-system A) = refl-htpy

--   comp-hom-system :
--     {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : system l3 l4}
--     {C : system l5 l6} (g : hom-system B C) (f : hom-system A B) →
--     hom-system A C
--   section-system.type (comp-hom-system g f) =
--     section-system.type g ∘ section-system.type f
--   section-system.element (comp-hom-system g f) =
--     section-system.element g ∘ section-system.element f
--   section-system.ft (comp-hom-system {C = C} g f) X =
--     ( section-system.ft g (section-system.type f X)) ∙
--     ( ap (section-system.type g) (section-system.ft f X))
--   section-system.∂ (comp-hom-system g f) x =
--     ( section-system.∂ g (section-system.element f x)) ∙
--     ( ap (section-system.type g) (section-system.∂ f x))

--   constant-bifibered-system :
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2}
--     (B : fibered-system l3 l4 A) {C : system l5 l6}
--     (D : fibered-system l7 l8 C) →
--     bifibered-system l7 l8 B (constant-fibered-system A C)
--   bifibered-system.type (constant-bifibered-system B D) Y =
--     fibered-system.type D
--   bifibered-system.element (constant-bifibered-system B D) y =
--     fibered-system.element D
--   bifibered-system.ft (constant-bifibered-system B D) =
--     fibered-system.ft D
--   bifibered-system.∂ (constant-bifibered-system B D) =
--     fibered-system.∂ D

--   hom-fibered-system :
--     {l1 l2 l3 l4 l5 l6 l7 l8 : Level} {A : system l1 l2} {C : system l5 l6}
--     (f : hom-system A C)
--     (B : fibered-system l3 l4 A) (D : fibered-system l7 l8 C) →
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l7 ⊔ l8)
--   hom-fibered-system f B D =
--     section-fibered-system (constant-bifibered-system B D) f

--   id-hom-fibered-system :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} (B : fibered-system l3 l4 A) →
--     hom-fibered-system (id-hom-system A) B B
--   section-fibered-system.type (id-hom-fibered-system B) = id
--   section-fibered-system.element (id-hom-fibered-system B) = id
--   section-fibered-system.ft (id-hom-fibered-system B) = refl-htpy
--   section-fibered-system.∂ (id-hom-fibered-system B) = refl-htpy

--   postcomp-section-system :
--     {l1 l2 l3 l4 l5 l6 : Level} {A : system l1 l2} {B : fibered-system l3 l4 A}
--     {C : fibered-system l5 l6 A} (f : section-system B) →
--     hom-fibered-system (id-hom-system A) B C → section-system C
--   section-system.type (postcomp-section-system f h) X =
--     section-fibered-system.type h (section-system.type f X)
--   section-system.element (postcomp-section-system f h) x =
--     section-fibered-system.element h (section-system.element f x)
--   section-system.ft (postcomp-section-system f h) X =
--     ( section-fibered-system.ft h (section-system.type f X)) ∙
--     ( ap (section-fibered-system.type h) (section-system.ft f X))
--   section-system.∂ (postcomp-section-system f h) x =
--     ( section-fibered-system.∂ h (section-system.element f x)) ∙
--     ( ap (section-fibered-system.type h) (section-system.∂ f x))

--   slice-constant-fibered-system-ft :
--     {l1 l2 l3 l4 : Level} (A : system l1 l2) (B : system l3 l4) {n : ℕ}
--     (X : system.type A n) (Y : system.type B n) →
--     hom-fibered-system
--       ( id-hom-system (slice-system-ft A X))
--       ( slice-fibered-system-ft (constant-fibered-system A B) {n} {X} Y)
--       ( constant-fibered-system (slice-system-ft A X) (slice-system-ft B Y))
--   slice-constant-fibered-system-ft A B {zero-ℕ} X Y =
--     id-hom-fibered-system
--       ( slice-fibered-system-ft (constant-fibered-system A B) {zero-ℕ} {X} Y)
--   slice-constant-fibered-system-ft A B {succ-ℕ n} X Y =
--     id-hom-fibered-system
--       ( slice-fibered-system-ft (constant-fibered-system A B) {succ-ℕ n} {X} Y)

--   slice-hom-system-ft :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
--     (f : hom-system A B) {n : ℕ} (X : system.type A n) →
--     hom-system
--       ( slice-system-ft A X)
--       ( slice-system-ft B (section-system.type f X))
--   slice-hom-system-ft {A = A} {B} f X =
--     slice-section-system-ft f X

--   weakening : {l1 l2 : Level} (A : system l1 l2) → UU (l1 ⊔ l2)
--   weakening A =
--     {n : ℕ} (X : system.type A n) →
--     hom-system (slice-system-ft A X) (slice-system A X)

--   preserves-weakening :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
--     (WA : weakening A) (WB : weakening B) (f : hom-system A B) →
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--   preserves-weakening {A = A} {B} WA WB f =
--     {n : ℕ} (X : system.type A n) →
--     htpy-section-system
--       ( comp-hom-system
--         ( slice-section-system f X)
--         ( WA X))
--       ( comp-hom-system
--         ( WB (section-system.type f X))
--         ( slice-hom-system-ft f X))

--   substitution : {l1 l2 : Level} (A : system l1 l2) → UU (l1 ⊔ l2)
--   substitution A =
--     {n : ℕ} {X : system.type A n} (x : system.element A n)
--     (p : Id (system.∂ A x) X) → 
--     hom-system (slice-system A X) (slice-system-ft A X)

--   preserves-substitution :
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
--     (SA : substitution A) (SB : substitution B) (f : hom-system A B) →
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--   preserves-substitution {A = A} {B} SA SB f =
--     {n : ℕ} {X : system.type A n} (x : system.element A n) →
--     (p : Id (system.∂ A x) X) →
--     htpy-section-system
--       ( comp-hom-system (slice-hom-system-ft f X) (SA x p))
--       ( comp-hom-system
--         ( SB { n}
--              { section-system.type f X}
--              ( section-system.element f x)
--              ( (section-system.∂ f x) ∙ (ap (section-system.type f) p)))
--         ( slice-hom-system f X))

--   record generic-element
--     {l1 l2 : Level} {A : system l1 l2} (W : weakening A) : UU (l1 ⊔ l2)
--     where
--     field
--       δ : {n : ℕ} (X : system.type A n) → system.element A (succ-ℕ n)
--       γ : {n : ℕ} (X : system.type A n) →
--           Id (system.∂ A (δ X)) (section-system.type (W X) X)

--   record preserves-generic-element
--     {l1 l2 l3 l4 : Level} {A : system l1 l2} {B : system l3 l4}
--     {f : hom-system A B} {WA : weakening A} {WB : weakening B}
--     (Wf : preserves-weakening WA WB f)
--     (δA : generic-element {A = A} WA) (δB : generic-element {A = B} WB) :
--     UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
--     where
--     field
--       δ : {n : ℕ} (X : system.type A n) →
--           Id ( section-system.element f (generic-element.δ δA X))
--              ( generic-element.δ δB (section-system.type f X))
--       γ : {n : ℕ} (X : system.type A n) →
--           Id {!ap (system.∂ A) (δ X)!} {!!}
    

-- --------------------------------------------------------------------------------

-- {- We define the interpretation of type theory in B-systems -}

-- open B

-- -}
