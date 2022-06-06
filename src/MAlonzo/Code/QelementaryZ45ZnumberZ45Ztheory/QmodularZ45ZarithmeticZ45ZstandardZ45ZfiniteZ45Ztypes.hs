{-# LANGUAGE BangPatterns, EmptyDataDecls, EmptyCase,
             ExistentialQuantification, ScopedTypeVariables,
             NoMonomorphismRestriction, RankNTypes, PatternSynonyms,
             OverloadedStrings #-}
module MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmodularZ45ZarithmeticZ45ZstandardZ45ZfiniteZ45Ztypes where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers
import qualified MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes
import qualified MAlonzo.Code.QfoundationZ45Zcore.Qfunctions
import qualified MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes
import qualified MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes
import qualified MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes

-- elementary-number-theory.modular-arithmetic-standard-finite-types.mod-succ-ℕ
d_mod'45'succ'45'ℕ_6 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_mod'45'succ'45'ℕ_6 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_zero'45'Fin_230
             (coe v0)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_succ'45'Fin_270
             (coe addInt (coe (1 :: Integer)) (coe v0))
             (coe d_mod'45'succ'45'ℕ_6 (coe v0) (coe v2))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.mod-two-ℕ
d_mod'45'two'45'ℕ_14 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_mod'45'two'45'ℕ_14
  = coe d_mod'45'succ'45'ℕ_6 (coe (1 :: Integer))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.mod-three-ℕ
d_mod'45'three'45'ℕ_16 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_mod'45'three'45'ℕ_16
  = coe d_mod'45'succ'45'ℕ_6 (coe (2 :: Integer))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.cong-nat-succ-Fin
d_cong'45'nat'45'succ'45'Fin_22 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'nat'45'succ'45'Fin_22 ~v0 v1
  = du_cong'45'nat'45'succ'45'Fin_22 v1
du_cong'45'nat'45'succ'45'Fin_22 ::
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'nat'45'succ'45'Fin_22 v0
  = case coe v0 of
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inl_22 v1
        -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_cong'45'identification'45'ℕ_116
      MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.C_inr_24 v1
        -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_cong'45'zero'45'ℕ''_152
      _ -> MAlonzo.RTE.mazUnreachableError
-- elementary-number-theory.modular-arithmetic-standard-finite-types.cong-nat-mod-succ-ℕ
d_cong'45'nat'45'mod'45'succ'45'ℕ_34 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'nat'45'mod'45'succ'45'ℕ_34 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_cong'45'is'45'zero'45'nat'45'zero'45'Fin_330
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.d_trans'45'cong'45'ℕ_164
             (coe addInt (coe (1 :: Integer)) (coe v0))
             (coe
                MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe d_mod'45'succ'45'ℕ_6 (coe v0) (coe v1)))
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
                   (coe addInt (coe (1 :: Integer)) (coe v0))
                   (coe d_mod'45'succ'45'ℕ_6 (coe v0) (coe v2))))
             (coe v1)
             (coe
                du_cong'45'nat'45'succ'45'Fin_22
                (coe d_mod'45'succ'45'ℕ_6 (coe v0) (coe v2)))
             (coe d_cong'45'nat'45'mod'45'succ'45'ℕ_34 (coe v0) (coe v2))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.cong-eq-mod-succ-ℕ
d_cong'45'eq'45'mod'45'succ'45'ℕ_48 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'eq'45'mod'45'succ'45'ℕ_48 v0 v1 v2 ~v3
  = du_cong'45'eq'45'mod'45'succ'45'ℕ_48 v0 v1 v2
du_cong'45'eq'45'mod'45'succ'45'ℕ_48 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_cong'45'eq'45'mod'45'succ'45'ℕ_48 v0 v1 v2
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_concatenate'45'cong'45'eq'45'cong'45'ℕ_234
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
         (coe addInt (coe (1 :: Integer)) (coe v0))
         (coe d_mod'45'succ'45'ℕ_6 (coe v0) (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_symm'45'cong'45'ℕ_128
         (coe d_cong'45'nat'45'mod'45'succ'45'ℕ_34 (coe v0) (coe v1)))
      (coe d_cong'45'nat'45'mod'45'succ'45'ℕ_34 (coe v0) (coe v2))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.eq-mod-succ-cong-ℕ
d_eq'45'mod'45'succ'45'cong'45'ℕ_64 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_eq'45'mod'45'succ'45'cong'45'ℕ_64 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-zero-mod-succ-ℕ
d_is'45'zero'45'mod'45'succ'45'ℕ_78 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'zero'45'mod'45'succ'45'ℕ_78 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.div-is-zero-mod-succ-ℕ
d_div'45'is'45'zero'45'mod'45'succ'45'ℕ_90 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'is'45'zero'45'mod'45'succ'45'ℕ_90 v0 v1 ~v2
  = du_div'45'is'45'zero'45'mod'45'succ'45'ℕ_90 v0 v1
du_div'45'is'45'zero'45'mod'45'succ'45'ℕ_90 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'is'45'zero'45'mod'45'succ'45'ℕ_90 v0 v1
  = coe
      du_cong'45'eq'45'mod'45'succ'45'ℕ_48 (coe v0) (coe v1)
      (coe (0 :: Integer))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.issec-nat-Fin
d_issec'45'nat'45'Fin_102 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_issec'45'nat'45'Fin_102 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-split-surjective-mod-succ-ℕ
d_is'45'split'45'surjective'45'mod'45'succ'45'ℕ_110 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'split'45'surjective'45'mod'45'succ'45'ℕ_110 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
         (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1))
      erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.add-Fin
d_add'45'Fin_122 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_add'45'Fin_122 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      d_mod'45'succ'45'ℕ_6 (coe v3)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v2)))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.add-Fin'
d_add'45'Fin''_132 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_add'45'Fin''_132 v0 v1 v2
  = coe d_add'45'Fin_122 (coe v0) (coe v2) (coe v1)
-- elementary-number-theory.modular-arithmetic-standard-finite-types.ap-add-Fin
d_ap'45'add'45'Fin_148 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'add'45'Fin_148 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.cong-add-Fin
d_cong'45'add'45'Fin_160 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'add'45'Fin_160 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      d_cong'45'nat'45'mod'45'succ'45'ℕ_34 (coe v3)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v2)))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.neg-Fin
d_neg'45'Fin_170 :: Integer -> AgdaAny -> AgdaAny
d_neg'45'Fin_170 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      d_mod'45'succ'45'ℕ_6 (coe v2)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v1))
         (coe v0))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.cong-neg-Fin
d_cong'45'neg'45'Fin_180 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'neg'45'Fin_180 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      d_cong'45'nat'45'mod'45'succ'45'ℕ_34 (coe v2)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdistanceZ45ZnaturalZ45Znumbers.d_dist'45'ℕ_4
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v1))
         (coe v0))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.congruence-add-ℕ
d_congruence'45'add'45'ℕ_196 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_congruence'45'add'45'ℕ_196 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.d_trans'45'cong'45'ℕ_164
      (coe v0)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
         (coe v1) (coe v2))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
         (coe v1) (coe v4))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QadditionZ45ZnaturalZ45Znumbers.d_add'45'ℕ_4
         (coe v3) (coe v4))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_translation'45'invariant'45'cong'45'ℕ_446
         (coe v6))
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QcongruenceZ45ZnaturalZ45Znumbers.du_translation'45'invariant'45'cong'45'ℕ''_480
         (coe v5))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.mod-succ-add-ℕ
d_mod'45'succ'45'add'45'ℕ_218 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mod'45'succ'45'add'45'ℕ_218 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.commutative-add-Fin
d_commutative'45'add'45'Fin_232 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'add'45'Fin_232 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.associative-add-Fin
d_associative'45'add'45'Fin_248 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'add'45'Fin_248 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-unit-law-add-Fin
d_right'45'unit'45'law'45'add'45'Fin_262 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'add'45'Fin_262 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-unit-law-add-Fin
d_left'45'unit'45'law'45'add'45'Fin_272 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'add'45'Fin_272 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-inverse-law-add-Fin
d_left'45'inverse'45'law'45'add'45'Fin_282 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'inverse'45'law'45'add'45'Fin_282 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-inverse-law-add-Fin
d_right'45'inverse'45'law'45'add'45'Fin_292 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'inverse'45'law'45'add'45'Fin_292 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-add-one-succ-Fin'
d_is'45'add'45'one'45'succ'45'Fin''_300 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'one'45'succ'45'Fin''_300 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-add-one-succ-Fin
d_is'45'add'45'one'45'succ'45'Fin_310 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'one'45'succ'45'Fin_310 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-successor-law-add-Fin
d_right'45'successor'45'law'45'add'45'Fin_320 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'add'45'Fin_320 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-successor-law-add-Fin
d_left'45'successor'45'law'45'add'45'Fin_334 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'add'45'Fin_334 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.mul-Fin
d_mul'45'Fin_342 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_mul'45'Fin_342 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      d_mod'45'succ'45'ℕ_6 (coe v3)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v2)))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.mul-Fin'
d_mul'45'Fin''_352 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_mul'45'Fin''_352 v0 v1 v2
  = coe d_mul'45'Fin_342 (coe v0) (coe v2) (coe v1)
-- elementary-number-theory.modular-arithmetic-standard-finite-types.ap-mul-Fin
d_ap'45'mul'45'Fin_370 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_ap'45'mul'45'Fin_370 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.cong-mul-Fin
d_cong'45'mul'45'Fin_382 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_cong'45'mul'45'Fin_382 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      d_cong'45'nat'45'mod'45'succ'45'ℕ_34 (coe v3)
      (coe
         MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QmultiplicationZ45ZnaturalZ45Znumbers.d_mul'45'ℕ_4
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.QunivalentZ45Zcombinatorics.QstandardZ45ZfiniteZ45Ztypes.d_nat'45'Fin_152
            (coe v0) (coe v2)))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.associative-mul-Fin
d_associative'45'mul'45'Fin_398 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_associative'45'mul'45'Fin_398 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.commutative-mul-Fin
d_commutative'45'mul'45'Fin_414 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_commutative'45'mul'45'Fin_414 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-unit-law-mul-Fin
d_left'45'unit'45'law'45'mul'45'Fin_426 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'unit'45'law'45'mul'45'Fin_426 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-unit-law-mul-Fin
d_right'45'unit'45'law'45'mul'45'Fin_436 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'unit'45'law'45'mul'45'Fin_436 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-zero-law-mul-Fin
d_left'45'zero'45'law'45'mul'45'Fin_444 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'zero'45'law'45'mul'45'Fin_444 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-zero-law-mul-Fin
d_right'45'zero'45'law'45'mul'45'Fin_454 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'zero'45'law'45'mul'45'Fin_454 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-distributive-mul-add-Fin
d_left'45'distributive'45'mul'45'add'45'Fin_466 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'distributive'45'mul'45'add'45'Fin_466 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-distributive-mul-add-Fin
d_right'45'distributive'45'mul'45'add'45'Fin_484 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'distributive'45'mul'45'add'45'Fin_484 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.add-add-neg-Fin
d_add'45'add'45'neg'45'Fin_500 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'add'45'neg'45'Fin_500 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.add-neg-add-Fin
d_add'45'neg'45'add'45'Fin_514 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'neg'45'add'45'Fin_514 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-equiv-add-Fin
d_is'45'equiv'45'add'45'Fin_526 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'add'45'Fin_526 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'Fin_122 (coe v0) (coe d_neg'45'Fin_170 (coe v0) (coe v1)))
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'Fin_122 (coe v0) (coe d_neg'45'Fin_170 (coe v0) (coe v1)))
         erased)
-- elementary-number-theory.modular-arithmetic-standard-finite-types.equiv-add-Fin
d_equiv'45'add'45'Fin_540 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'add'45'Fin_540 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_add'45'Fin_122 (coe v0) (coe v1))
      (coe d_is'45'equiv'45'add'45'Fin_526 (coe v0) (coe v1))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.add-add-neg-Fin'
d_add'45'add'45'neg'45'Fin''_552 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'add'45'neg'45'Fin''_552 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.add-neg-add-Fin'
d_add'45'neg'45'add'45'Fin''_566 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_add'45'neg'45'add'45'Fin''_566 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-equiv-add-Fin'
d_is'45'equiv'45'add'45'Fin''_578 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'add'45'Fin''_578 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'Fin''_132 (coe v0)
            (coe d_neg'45'Fin_170 (coe v0) (coe v1)))
         erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            d_add'45'Fin''_132 (coe v0)
            (coe d_neg'45'Fin_170 (coe v0) (coe v1)))
         erased)
-- elementary-number-theory.modular-arithmetic-standard-finite-types.equiv-add-Fin'
d_equiv'45'add'45'Fin''_592 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'add'45'Fin''_592 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_add'45'Fin''_132 (coe v0) (coe v1))
      (coe d_is'45'equiv'45'add'45'Fin''_578 (coe v0) (coe v1))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-injective-add-Fin
d_is'45'injective'45'add'45'Fin_602 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'Fin_602 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-injective-add-Fin'
d_is'45'injective'45'add'45'Fin''_618 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'injective'45'add'45'Fin''_618 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.mul-neg-one-Fin
d_mul'45'neg'45'one'45'Fin_634 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_mul'45'neg'45'one'45'Fin_634 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-one-neg-neg-one-Fin
d_is'45'one'45'neg'45'neg'45'one'45'Fin_642 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'one'45'neg'45'neg'45'one'45'Fin_642 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-neg-one-neg-one-Fin
d_is'45'neg'45'one'45'neg'45'one'45'Fin_648 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'neg'45'one'45'neg'45'one'45'Fin_648 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-add-neg-one-pred-Fin'
d_is'45'add'45'neg'45'one'45'pred'45'Fin''_656 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'neg'45'one'45'pred'45'Fin''_656 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-add-neg-one-pred-Fin
d_is'45'add'45'neg'45'one'45'pred'45'Fin_666 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'add'45'neg'45'one'45'pred'45'Fin_666 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-mul-neg-one-neg-Fin
d_is'45'mul'45'neg'45'one'45'neg'45'Fin_674 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'mul'45'neg'45'one'45'neg'45'Fin_674 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-mul-neg-one-neg-Fin'
d_is'45'mul'45'neg'45'one'45'neg'45'Fin''_682 ::
  Integer ->
  MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12 ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_is'45'mul'45'neg'45'one'45'neg'45'Fin''_682 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.neg-zero-Fin
d_neg'45'zero'45'Fin_688 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'zero'45'Fin_688 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.neg-succ-Fin
d_neg'45'succ'45'Fin_696 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'succ'45'Fin_696 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.neg-pred-Fin
d_neg'45'pred'45'Fin_706 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'pred'45'Fin_706 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.distributive-neg-add-Fin
d_distributive'45'neg'45'add'45'Fin_718 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_distributive'45'neg'45'add'45'Fin_718 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-predecessor-law-add-Fin
d_left'45'predecessor'45'law'45'add'45'Fin_732 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'predecessor'45'law'45'add'45'Fin_732 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-predecessor-law-add-Fin
d_right'45'predecessor'45'law'45'add'45'Fin_746 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'predecessor'45'law'45'add'45'Fin_746 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-negative-law-mul-Fin
d_left'45'negative'45'law'45'mul'45'Fin_760 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'negative'45'law'45'mul'45'Fin_760 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-negative-law-mul-Fin
d_right'45'negative'45'law'45'mul'45'Fin_774 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'negative'45'law'45'mul'45'Fin_774 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-successor-law-mul-Fin
d_left'45'successor'45'law'45'mul'45'Fin_788 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'successor'45'law'45'mul'45'Fin_788 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-successor-law-mul-Fin
d_right'45'successor'45'law'45'mul'45'Fin_802 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'successor'45'law'45'mul'45'Fin_802 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.left-predecessor-law-mul-Fin
d_left'45'predecessor'45'law'45'mul'45'Fin_816 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_left'45'predecessor'45'law'45'mul'45'Fin_816 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.right-predecessor-law-mul-Fin
d_right'45'predecessor'45'law'45'mul'45'Fin_830 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_right'45'predecessor'45'law'45'mul'45'Fin_830 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.leq-nat-mod-succ-ℕ
d_leq'45'nat'45'mod'45'succ'45'ℕ_842 ::
  Integer -> Integer -> AgdaAny
d_leq'45'nat'45'mod'45'succ'45'ℕ_842 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-decidable-div-ℕ
d_is'45'decidable'45'div'45'ℕ_854 ::
  Integer ->
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'div'45'ℕ_854 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
             (\ v2 ->
                coe
                  MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.du_div'45'eq'45'ℕ_504)
             (coe
                MAlonzo.Code.QfoundationZ45Zcore.Qfunctions.du__'8728'__36 erased
                erased)
             (coe
                MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QequalityZ45ZnaturalZ45Znumbers.d_is'45'decidable'45'is'45'zero'45'ℕ''_102
                (coe v1))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'iff_250
             (\ v3 ->
                coe du_div'45'is'45'zero'45'mod'45'succ'45'ℕ_90 (coe v2) (coe v1))
             erased
             (coe
                MAlonzo.Code.QunivalentZ45Zcombinatorics.QequalityZ45ZstandardZ45ZfiniteZ45Ztypes.d_is'45'decidable'45'is'45'zero'45'Fin_124
                (coe v0) (coe d_mod'45'succ'45'ℕ_6 (coe v2) (coe v1)))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.div-ℕ-decidable-Prop
d_div'45'ℕ'45'decidable'45'Prop_866 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10 ->
   MAlonzo.Code.QfoundationZ45Zcore.QemptyZ45Ztypes.T_empty_4) ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_div'45'ℕ'45'decidable'45'Prop_866 v0 v1 ~v2
  = du_div'45'ℕ'45'decidable'45'Prop_866 v0 v1
du_div'45'ℕ'45'decidable'45'Prop_866 ::
  Integer ->
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
du_div'45'ℕ'45'decidable'45'Prop_866 v0 v1
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      erased
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe
            MAlonzo.Code.QelementaryZ45ZnumberZ45Ztheory.QdivisibilityZ45ZnaturalZ45Znumbers.du_is'45'prop'45'div'45'ℕ_128)
         (coe d_is'45'decidable'45'div'45'ℕ_854 (coe v0) (coe v1)))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-decidable-is-even-ℕ
d_is'45'decidable'45'is'45'even'45'ℕ_888 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'even'45'ℕ_888 v0
  = coe
      d_is'45'decidable'45'div'45'ℕ_854 (coe (2 :: Integer)) (coe v0)
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-decidable-is-odd-ℕ
d_is'45'decidable'45'is'45'odd'45'ℕ_894 ::
  Integer -> MAlonzo.Code.Qfoundation.QcoproductZ45Ztypes.T_coprod_12
d_is'45'decidable'45'is'45'odd'45'ℕ_894 v0
  = coe
      MAlonzo.Code.Qfoundation.QdecidableZ45Ztypes.du_is'45'decidable'45'neg_234
      (coe d_is'45'decidable'45'is'45'even'45'ℕ_888 (coe v0))
-- elementary-number-theory.modular-arithmetic-standard-finite-types.neg-neg-Fin
d_neg'45'neg'45'Fin_902 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.QfoundationZ45Zcore.QidentityZ45Ztypes.T_Id_10
d_neg'45'neg'45'Fin_902 = erased
-- elementary-number-theory.modular-arithmetic-standard-finite-types.is-equiv-neg-Fin
d_is'45'equiv'45'neg'45'Fin_910 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_is'45'equiv'45'neg'45'Fin_910 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_neg'45'Fin_170 (coe v0)) erased)
      (coe
         MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
         (coe d_neg'45'Fin_170 (coe v0)) erased)
-- elementary-number-theory.modular-arithmetic-standard-finite-types.equiv-neg-Fin
d_equiv'45'neg'45'Fin_914 ::
  Integer ->
  MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.T_Σ_12
d_equiv'45'neg'45'Fin_914 v0
  = coe
      MAlonzo.Code.QfoundationZ45Zcore.QdependentZ45ZpairZ45Ztypes.C_pair_30
      (coe d_neg'45'Fin_170 (coe v0))
      (coe d_is'45'equiv'45'neg'45'Fin_910 (coe v0))
