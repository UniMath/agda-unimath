# Group solver

```agda
module reflection.group-solver where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.identity-types
open import foundation.universe-levels

open import group-theory.groups

open import linear-algebra.vectors

open import lists.concatenation-lists
open import lists.functoriality-lists
open import lists.lists
open import lists.reversing-lists
```

</details>

## Idea

This module simplifies group expressions, such that all items associate the same
way and removes units and inverses next to the original.

The main entry-point is `solveExpr` below

```agda
data Fin : ℕ → UU lzero where
  zero-Fin : ∀ {n} → Fin (succ-ℕ n)
  succ-Fin : ∀ {n} → Fin n → Fin (succ-ℕ n)

finEq : ∀ {n} → (a b : Fin n) → is-decidable (Id a b)
finEq zero-Fin zero-Fin = inl refl
finEq zero-Fin (succ-Fin b) = inr (λ ())
finEq (succ-Fin a) zero-Fin = inr (λ ())
finEq (succ-Fin a) (succ-Fin b) with finEq a b
... | inl eq = inl (ap succ-Fin eq)
... | inr neq = inr (λ where refl → neq refl)

getVec : ∀ {n} {l} {A : UU l} → vec A n → Fin n → A
getVec (x ∷ v) zero-Fin = x
getVec (x ∷ v) (succ-Fin k) = getVec v k

data GroupSyntax (n : ℕ) : UU where
  gUnit : GroupSyntax n
  gMul : GroupSyntax n → GroupSyntax n → GroupSyntax n
  gInv : GroupSyntax n → GroupSyntax n
  inner : Fin n → GroupSyntax n

data SimpleElem (n : ℕ) : UU where
  inv-SE : Fin n → SimpleElem n
  pure-SE : Fin n → SimpleElem n

inv-SE' : ∀ {n} → SimpleElem n → SimpleElem n
inv-SE' (inv-SE k) = pure-SE k
inv-SE' (pure-SE k) = inv-SE k

Simple : (n : ℕ) → UU
Simple n = list (SimpleElem n)

module _ {n : ℕ} where
  unquoteSimpleElem : SimpleElem n → GroupSyntax n
  unquoteSimpleElem (inv-SE x) = gInv (inner x)
  unquoteSimpleElem (pure-SE x) = inner x

  unquoteSimpleNonEmpty : Simple n → GroupSyntax n → GroupSyntax n
  unquoteSimpleNonEmpty nil x = x
  unquoteSimpleNonEmpty (cons y xs) x =
    gMul (unquoteSimpleNonEmpty xs (unquoteSimpleElem y)) x

  unquoteSimple : Simple n → GroupSyntax n
  unquoteSimple nil = gUnit
  unquoteSimple (cons x xs) = unquoteSimpleNonEmpty xs (unquoteSimpleElem x)

  elim-inverses : SimpleElem n → Simple n → Simple n
  elim-inverses x nil = cons x nil
  elim-inverses xi@(inv-SE x) yxs@(cons (inv-SE y) xs) = cons xi yxs
  elim-inverses xi@(inv-SE x) yxs@(cons (pure-SE y) xs) with finEq x y
  ... | inl eq = xs
  ... | inr neq = cons xi yxs
  elim-inverses xi@(pure-SE x) yxs@(cons (inv-SE y) xs) with finEq x y
  ... | inl eq = xs
  ... | inr neq = cons xi yxs
  elim-inverses xi@(pure-SE x) yxs@(cons (pure-SE y) xs) = cons xi yxs

  concat-simplify : Simple n → Simple n → Simple n
  concat-simplify nil b = b
  concat-simplify (cons x a) b = elim-inverses x (concat-simplify a b)

  simplifyGS : GroupSyntax n → Simple n
  simplifyGS gUnit = nil
  simplifyGS (gMul a b) = concat-simplify (simplifyGS b) (simplifyGS a)
  simplifyGS (gInv a) = reverse-list (map-list inv-SE' (simplifyGS a))
  -- simplifyGS (gInv a) = map-list inv-SE' (reverse-list (simplifyGS a))
  simplifyGS (inner n) = cons (pure-SE n) nil

  data GroupEqualityElem : GroupSyntax n → GroupSyntax n → UU where
    -- equivalence relation
    xsym-GE : ∀ {x} {y} → GroupEqualityElem x y → GroupEqualityElem y x

    -- Variations on ap
    -- xap-gMul : ∀ {x} {y} {z} {w} → GroupEqualityElem x y → GroupEqualityElem z w → GroupEqualityElem (gMul x z) (gMul y w)
    xap-gMul-l :
      ∀ {x} {y} {z} →
      GroupEqualityElem x y → GroupEqualityElem (gMul x z) (gMul y z)
    xap-gMul-r :
      ∀ {x} {y} {z} →
      GroupEqualityElem y z → GroupEqualityElem (gMul x y) (gMul x z)
    xap-gInv :
      ∀ {x} {y} →
      GroupEqualityElem x y → GroupEqualityElem (gInv x) (gInv y)

    -- Group laws
    xassoc-GE :
      ∀ x y z → GroupEqualityElem (gMul (gMul x y) z) (gMul x (gMul y z))
    xl-unit : ∀ x → GroupEqualityElem (gMul gUnit x) x
    xr-unit : ∀ x → GroupEqualityElem (gMul x gUnit) x
    xl-inv : ∀ x → GroupEqualityElem (gMul (gInv x) x) gUnit
    xr-inv : ∀ x → GroupEqualityElem (gMul x (gInv x)) gUnit

    -- Theorems that are provable from the others
    xinv-unit-GE : GroupEqualityElem (gInv gUnit) gUnit
    xinv-inv-GE : ∀ x → GroupEqualityElem (gInv (gInv x)) x
    xdistr-inv-mul-GE :
      ∀ x y → GroupEqualityElem (gInv (gMul x y)) (gMul (gInv y) (gInv x))
  data GroupEquality : GroupSyntax n → GroupSyntax n → UU where
    refl-GE : ∀ {x} → GroupEquality x x
    _∷GE_ :
      ∀ {x} {y} {z} →
      GroupEqualityElem x y → GroupEquality y z → GroupEquality x z

  infixr 10 _∷GE_

  module _ where
    -- equivalence relation
    singleton-GE : ∀ {x y} → GroupEqualityElem x y → GroupEquality x y
    singleton-GE x = x ∷GE refl-GE

    _∙GE_ :
      ∀ {x} {y} {z} → GroupEquality x y → GroupEquality y z → GroupEquality x z
    refl-GE ∙GE b = b
    (x ∷GE a) ∙GE b = x ∷GE (a ∙GE b)
    infixr 15 _∙GE_

    sym-GE : ∀ {x} {y} → GroupEquality x y → GroupEquality y x
    sym-GE refl-GE = refl-GE
    sym-GE (a ∷GE as) = sym-GE as ∙GE singleton-GE (xsym-GE a)

    -- Variations on ap
    ap-gInv : ∀ {x} {y} → GroupEquality x y → GroupEquality (gInv x) (gInv y)
    ap-gInv refl-GE = refl-GE
    ap-gInv (a ∷GE as) = xap-gInv a ∷GE ap-gInv as
    ap-gMul-l :
      ∀ {x} {y} {z} → GroupEquality x y → GroupEquality (gMul x z) (gMul y z)
    ap-gMul-l refl-GE = refl-GE
    ap-gMul-l (x ∷GE xs) = xap-gMul-l x ∷GE ap-gMul-l xs
    ap-gMul-r :
      ∀ {x} {y} {z} → GroupEquality y z → GroupEquality (gMul x y) (gMul x z)
    ap-gMul-r refl-GE = refl-GE
    ap-gMul-r (x ∷GE xs) = xap-gMul-r x ∷GE ap-gMul-r xs
    ap-gMul :
      ∀ {x} {y} {z} {w} →
      GroupEquality x y → GroupEquality z w →
      GroupEquality (gMul x z) (gMul y w)
    ap-gMul p q = ap-gMul-l p ∙GE ap-gMul-r q

    -- Group laws
    assoc-GE : ∀ x y z → GroupEquality (gMul (gMul x y) z) (gMul x (gMul y z))
    assoc-GE x y z = singleton-GE (xassoc-GE x y z)
    l-unit : ∀ x → GroupEquality (gMul gUnit x) x
    l-unit x = singleton-GE (xl-unit x)
    r-unit : ∀ x → GroupEquality (gMul x gUnit) x
    r-unit x = singleton-GE (xr-unit x)
    l-inv : ∀ x → GroupEquality (gMul (gInv x) x) gUnit
    l-inv x = singleton-GE (xl-inv x)
    r-inv : ∀ x → GroupEquality (gMul x (gInv x)) gUnit
    r-inv x = singleton-GE (xr-inv x)

    -- Theorems that are provable from the others
    inv-unit-GE : GroupEquality (gInv gUnit) gUnit
    inv-unit-GE = singleton-GE (xinv-unit-GE)
    inv-inv-GE : ∀ x → GroupEquality (gInv (gInv x)) x
    inv-inv-GE x = singleton-GE (xinv-inv-GE x)
    distr-inv-mul-GE :
      ∀ x y → GroupEquality (gInv (gMul x y)) (gMul (gInv y) (gInv x))
    distr-inv-mul-GE x y = singleton-GE (xdistr-inv-mul-GE x y)

  assoc-GE' : ∀ x y z → GroupEquality (gMul x (gMul y z)) (gMul (gMul x y) z)
  assoc-GE' x y z = sym-GE (assoc-GE x y z)

  elim-inverses-remove-valid :
    (b : list (SimpleElem n)) (w u : GroupSyntax n) →
    GroupEquality (gMul w u) gUnit →
    GroupEquality
      ( gMul (unquoteSimpleNonEmpty b w) u)
      ( unquoteSimple b)
  elim-inverses-remove-valid nil w u eq = eq
  elim-inverses-remove-valid (cons x b) w u eq =
    assoc-GE _ _ _ ∙GE
    ap-gMul-r eq ∙GE
    r-unit _

  elim-inverses-valid :
    (x : SimpleElem n) (b : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple b) (unquoteSimpleElem x))
      ( unquoteSimple (elim-inverses x b))
  elim-inverses-valid x nil = l-unit (unquoteSimpleElem x)
  elim-inverses-valid (inv-SE x) (cons (inv-SE y) b) = refl-GE
  elim-inverses-valid (inv-SE x) (cons (pure-SE y) b) with finEq x y
  ... | inl refl =
    elim-inverses-remove-valid b (inner x) (gInv (inner x)) (r-inv (inner x))
  ... | inr neq = refl-GE
  elim-inverses-valid (pure-SE x) (cons (inv-SE y) b) with finEq x y
  ... | inl refl =
    elim-inverses-remove-valid b (gInv (inner x)) (inner x) (l-inv (inner x))
  ... | inr neq = refl-GE
  elim-inverses-valid (pure-SE x) (cons (pure-SE y) b) = refl-GE

  concat-simplify-nonempty-valid :
    (x : SimpleElem n) (a : list (SimpleElem n)) (b : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple b) (unquoteSimple (cons x a)))
      ( unquoteSimple (concat-simplify (cons x a) b))
  concat-simplify-nonempty-valid x nil b = elim-inverses-valid x b
  concat-simplify-nonempty-valid x (cons y a) b =
    assoc-GE' _ _ _ ∙GE
    ap-gMul-l (concat-simplify-nonempty-valid y a b) ∙GE
    elim-inverses-valid x (elim-inverses y (concat-simplify a b))

  concat-simplify-valid :
    ∀ (u w : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple w) (unquoteSimple u))
      ( unquoteSimple (concat-simplify u w))
  concat-simplify-valid nil b = r-unit (unquoteSimple b)
  concat-simplify-valid (cons x a) b = concat-simplify-nonempty-valid x a b

  inv-single-valid :
    ∀ w →
    GroupEquality
      ( gInv (unquoteSimpleElem w))
      ( unquoteSimpleElem (inv-SE' w))
  inv-single-valid (inv-SE x) = inv-inv-GE (inner x)
  inv-single-valid (pure-SE x) = refl-GE

  gMul-concat-nonempty :
    (w : GroupSyntax n) (as b : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple b) (unquoteSimpleNonEmpty as w))
      ( unquoteSimpleNonEmpty (concat-list as b) w)
  gMul-concat-nonempty w nil nil = l-unit w
  gMul-concat-nonempty w nil (cons x b) = refl-GE
  gMul-concat-nonempty w (cons x as) b =
    assoc-GE' _ _ _ ∙GE
    ap-gMul-l (gMul-concat-nonempty (unquoteSimpleElem x) as b)

  gMul-concat' :
    (xs : Simple n) (ys : Simple n) →
    GroupEquality
      ( gMul (unquoteSimple ys) (unquoteSimple xs))
      ( unquoteSimple (concat-list xs ys))
  gMul-concat' nil bs = r-unit _
  gMul-concat' (cons x as) b = gMul-concat-nonempty (unquoteSimpleElem x) as b

  gMul-concat-1 :
    (xs : Simple n) (x : SimpleElem n) →
    GroupEquality
      ( gMul (unquoteSimpleElem x) (unquoteSimple xs))
      ( unquoteSimple (concat-list xs (cons x nil)))
  gMul-concat-1 xs a = gMul-concat' xs (cons a nil)

  -- inv-simplify-valid'-nonempty : ∀ (x : SimpleElem n) (xs : list (SimpleElem n)) →
  --                               GroupEquality (gInv (unquoteSimple (cons x xs)))
  --                               (unquoteSimple (reverse-list (map-list inv-SE' (cons x xs))))
  -- inv-simplify-valid'-nonempty x nil = inv-single-valid x
  -- inv-simplify-valid'-nonempty x (cons y xs) =
  --   distr-inv-mul-GE (unquoteSimple (cons y xs)) (unquoteSimpleElem x) ∙GE
  --   ap-gMul (inv-single-valid x) (inv-simplify-valid'-nonempty y xs) ∙GE
  --   gMul-concat-1 (concat-list (reverse-list (map-list inv-SE' xs)) (in-list (inv-SE' y))) (inv-SE' x)

  -- inv-simplify-valid' : ∀ (w : list (SimpleElem n)) →
  --                     GroupEquality (gInv (unquoteSimple w))
  --                     (unquoteSimple (reverse-list (map-list inv-SE' w)))
  -- inv-simplify-valid' nil = inv-unit-GE
  -- inv-simplify-valid' (cons x xs) =
  --   inv-simplify-valid'-nonempty x xs

  -- simplifyValid : ∀ (g : GroupSyntax n) → GroupEquality g (unquoteSimple (simplifyGS g))
  -- simplifyValid gUnit = refl-GE
  -- simplifyValid (gMul a b) =
  --   (ap-gMul (simplifyValid a) (simplifyValid b)) ∙GE
  --   (concat-simplify-valid (simplifyGS b) (simplifyGS a))
  -- simplifyValid (gInv g) = ap-gInv (simplifyValid g) ∙GE inv-simplify-valid' (simplifyGS g)
  -- simplifyValid (inner _) = refl-GE

  Env : ∀ {l} → ℕ → UU l → UU l
  Env n A = vec A n

  module _
    {l : Level} (G : Group l)
    where

    unQuoteGS : ∀ {n} → GroupSyntax n → Env n (type-Group G) → type-Group G
    unQuoteGS gUnit e = unit-Group G
    unQuoteGS (gMul x y) e = mul-Group G (unQuoteGS x e) (unQuoteGS y e)
    unQuoteGS (gInv x) e = inv-Group G (unQuoteGS x e)
    unQuoteGS (inner x) e = getVec e x

    private
      -- Shorter names to make the proofs less verbose
      _*_ = mul-Group G
      infixl 40 _*_
      _⁻¹ = inv-Group G
      infix 45 _⁻¹
      unit = unit-Group G

    useGroupEqualityElem :
      {x y : GroupSyntax n} (env : Env n (type-Group G)) →
      GroupEqualityElem x y → unQuoteGS x env ＝ unQuoteGS y env
    useGroupEqualityElem env (xsym-GE ge) = inv (useGroupEqualityElem env ge)
    useGroupEqualityElem env (xap-gMul-l {z = z} ge') =
      ap (_* unQuoteGS z env) (useGroupEqualityElem env ge')
    useGroupEqualityElem env (xap-gMul-r {x = x} ge') =
      ap (unQuoteGS x env *_) (useGroupEqualityElem env ge')
    -- useGroupEqualityElem env (xap-gMul {y = y} {z = z} ge ge') =
    --                              ap (_* (unQuoteGS z env)) (useGroupEqualityElem env ge)
    --                              ∙ ap (unQuoteGS y env *_) (useGroupEqualityElem env ge')
    useGroupEqualityElem env (xap-gInv ge) =
      ap (inv-Group G) (useGroupEqualityElem env ge)
    useGroupEqualityElem env (xassoc-GE x y z) = associative-mul-Group G _ _ _
    useGroupEqualityElem env (xl-unit _) = left-unit-law-mul-Group G _
    useGroupEqualityElem env (xr-unit _) = right-unit-law-mul-Group G _
    useGroupEqualityElem env (xl-inv x) = left-inverse-law-mul-Group G _
    useGroupEqualityElem env (xr-inv x) = right-inverse-law-mul-Group G _
    useGroupEqualityElem env xinv-unit-GE = inv-unit-Group G
    useGroupEqualityElem env (xinv-inv-GE x) = inv-inv-Group G (unQuoteGS x env)
    useGroupEqualityElem env (xdistr-inv-mul-GE x y) =
      distributive-inv-mul-Group G

    useGroupEquality :
      {x y : GroupSyntax n} (env : Env n (type-Group G)) →
      GroupEquality x y → unQuoteGS x env ＝ unQuoteGS y env
    useGroupEquality env refl-GE = refl
    useGroupEquality env (x ∷GE refl-GE) = useGroupEqualityElem env x
    useGroupEquality env (x ∷GE xs@(_ ∷GE _)) =
      useGroupEqualityElem env x ∙ useGroupEquality env xs

    -- simplifyExpression :
    --   ∀ (g : GroupSyntax n) (env : Env n (type-Group G)) →
    --   unQuoteGS g env ＝ unQuoteGS (unquoteSimple (simplifyGS g)) env
    -- simplifyExpression g env = useGroupEquality env (simplifyValid g)

    -- Variadic functions
    n-args : (n : ℕ) (A B : UU) → UU
    n-args zero-ℕ A B = B
    n-args (succ-ℕ n) A B = A → n-args n A B
    map-n-args :
      ∀ {A A' B : UU} (n : ℕ) → (A' → A) → n-args n A B → n-args n A' B
    map-n-args zero-ℕ f v = v
    map-n-args (succ-ℕ n) f v = λ x → map-n-args n f (v (f x))
    apply-n-args-fin : ∀ {B : UU} (n : ℕ) → n-args n (Fin n) B → B
    apply-n-args-fin zero-ℕ f = f
    apply-n-args-fin (succ-ℕ n) f =
      apply-n-args-fin n (map-n-args n succ-Fin (f zero-Fin))
    apply-n-args : ∀ {B : UU} (n : ℕ) → n-args n (GroupSyntax n) B → B
    apply-n-args n f = apply-n-args-fin n (map-n-args n inner f)

    -- A variation of simplifyExpression which takes a function from the free variables to expr
    -- simplifyExpr :
    --   ∀ (env : Env n (type-Group G)) (g : n-args n (GroupSyntax n) (GroupSyntax n)) →
    --   unQuoteGS (apply-n-args n g) env ＝ unQuoteGS (unquoteSimple (simplifyGS (apply-n-args n g))) env
    -- simplifyExpr env g = simplifyExpression (apply-n-args n g) env

    open import linear-algebra.vectors using (_∷_ ; empty-vec) public
```

```agda
-- private _\*'_ : ∀ {n} → GroupSyntax n → GroupSyntax n → GroupSyntax n _\*'_ =
-- gMul x : GroupSyntax 2 x = inner (zero-Fin) y : GroupSyntax 2 y = inner
-- (succ-Fin zero-Fin)

--     infixl 40 _*'_
--     ex1 : GroupEquality {n = 2} (gInv (x *' y *' gInv x *' gInv y)) (y *' x *' gInv y *' gInv x)
--     ex1 = simplifyValid _

--     ex2 : ∀ x y → (x * y * x ⁻¹ * y ⁻¹) ⁻¹ ＝ (y * x * y ⁻¹ * x ⁻¹)
--     ex2 x' y' = simplifyExpression (gInv (x *' y *' gInv x *' gInv y)) (x' ∷ y' ∷ empty-vec)

--     _ : UU
--     -- _ = {!simplifyValid (y *' (x *' (gInv y *' (gInv x *' gUnit))))!}
--     _ = {!ex1!}

--     ex3 : ∀ x y → (x * y) ⁻¹ ＝ (y ⁻¹ * x ⁻¹)
--     ex3 x' y' = {!simplifyExpression (gInv (x *' y)) (x' ∷ y' ∷ empty-vec)!}

--     _ : GroupEquality {n = 2} (y *' (x *' (gInv y *' (gInv x *' gUnit)))) (y *' (x *' (gInv y *' (gInv x *' gUnit))))
--     _ = {!simplifyValid (gInv x *' x *' y)!}
--     -- _ = {!simplifyValid (gUnit *' gUnit)!}
--     -- _ = {!simplifyValid (x *' gUnit)!}
```
